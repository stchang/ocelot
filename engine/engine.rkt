#lang typed/rosette

(require (only-in typed/rosette/base-forms unsafe-assign-type)
         (only-in rosette/safe #%expression)
         (except-in "../lang/util/extra-forms.rkt" and tup)
         "../lang/util/match.rkt"
         racket/require
         (matching-identifiers-in #rx"^node/.+$" "../lang/ast.rkt")
         (only-in "../lang/ast.rkt"
                  Node/Formula CNode/Formula Node/Expr CNode/Expr
                  relation-name relation-arity)
         "../lang/bounds.rkt" "../lang/universe.rkt"
         "matrix.rkt" "matrix-ops.rkt" "symmetry.rkt" "interpretation.rkt"
         (prefix-in $ "../lang/util/unlifted-ops.rkt"))

(provide interpret interpret*)

(define-type-alias RelationHash
  (CHashTable CNode/Expr CMatrix))

(define-type-alias CacheHash
  (CHashTable (CU CNode/Expr CNode/Formula) (U Matrix Bool)))
(define-type-alias Cache
  (CU CacheHash CFalse))

(: interpret : (C→ CNode/Formula CBounds Bool))
(define (interpret formula bounds)
  (let ([interp (instantiate-bounds bounds)])
    (interpret* formula interp)))

(: interpret* : (C→ CNode/Formula CInterpretation [#:cache? CBool] Bool))
(define (interpret* formula interp #:cache? [cache? #f])
  (match interp
    [(interpretation universe entries)
     (let ([relations (make-hash entries)])
       (assert-type
        (interpret-rec formula
                       universe
                       relations
                       (if cache? (ann (make-hash) : CacheHash) #f))
        : Bool))]))

;; the hash table is mutable!
(: interpret-rec : (C→ (CU CNode/Expr CNode/Formula) CUniverse RelationHash Cache (U Matrix Bool)))
(define (interpret-rec formula universe relations cache)
  ($if cache
       (hash-ref! (unsafe-assign-type (#%expression cache) : CacheHash)
                  formula
                  (λ () (interpret-body formula universe relations cache)))
       (interpret-body formula universe relations cache)))

(: interpret-body :
   (C→ (CU CNode/Expr CNode/Formula) CUniverse RelationHash Cache (U Matrix Bool)))
(define (interpret-body formula universe relations cache)
  (match formula
    [(node/expr/op arity args)
     (let ([args* (for/list ([a (in-list args)])
                    (interpret-rec a universe relations cache))])
       (interpret-expr-op universe
                          (unsafe-assign-type (#%expression formula) : CNode/Expr)
                          args*))]
    [(node/expr/relation arity name)
     (hash-ref relations
               (unsafe-assign-type (#%expression formula) : CNode/Expr)
       (λ () (error 'interpret "unbound relation ~a" formula)))]
    [(node/expr/constant arity type)
     (interpret-constant universe type)]
    [(node/expr/comprehension arity decls f)
     (let ([decls* (for/list ([d (in-list decls)])
                     (list (proj d 0) (interpret-rec (proj d 1) universe relations cache)))])
       (interpret-comprehension universe relations decls* f cache))]
    [(node/formula/op args)
     (interpret-formula-op universe relations formula args cache)]
    [(node/formula/quantified quantifier decls f)
     (let ([decls* (for/list ([d (in-list decls)])
                     (list (proj d 0) (interpret-rec (proj d 1) universe relations cache)))])
       (interpret-quantifier universe relations quantifier decls* f cache))]
    [(node/formula/multiplicity mult expr)
     (let ([expr* (interpret-rec expr universe relations cache)])
       (interpret-multiplicity universe mult expr*))]))


(: interpret-constant : (C→ CUniverse CSymbol Matrix))
(define (interpret-constant universe type)
  (match type
    ['none (matrix (make-list (universe-size universe) #f))]
    ['univ (matrix (make-list (universe-size universe) #t))]
    ['iden (let ([size (universe-size universe)])
             (matrix (for*/list ([i (in-range size)] [j (in-range size)])
                       (= i j))))]))


(: interpret-expr-op : (C→ CUniverse CNode/Expr (Listof Matrix) Matrix))
(define (interpret-expr-op universe op args)
  (match op
    [(? node/expr/op/+?)
     (matrix/nary-op universe matrix/or args)]
    [(? node/expr/op/&?)
     (matrix/nary-op universe matrix/and args)]
    [(? node/expr/op/-?)
     (matrix/nary-op universe matrix/difference args)]
    [(? node/expr/op/->?)
     (matrix/nary-op universe matrix/cross args)]
    [(? node/expr/op/~?)
     (matrix/transpose universe (first args))]
    [(? node/expr/op/join?)
     (matrix/nary-op universe matrix/dot args)]
    [(? node/expr/op/^?)
     (matrix/closure universe (first args))]
    [(? node/expr/op/*?)
     (let ([iden (interpret-constant universe 'iden)]
           [^A   (matrix/closure universe (first args))])
       (matrix/or universe ^A iden))]
    [(? node/expr/op/<:?)
     (matrix/domain universe (first args) (second args))]
    [(? node/expr/op/:>?)
     (matrix/range universe (first args) (second args))]))


(: interpret-comprehension : (C→ CUniverse RelationHash Any Any Cache Matrix))
(define (interpret-comprehension universe relations decls f cache)
  (define usize (universe-size universe))
  (define (comprehension* decls pre)
    (if (null? decls)
        (list (and pre (interpret-rec f universe relations (and cache (hash-copy cache)))))
        (match-let ([(list v r) (car decls)])
          (append* (for/list ([i usize][val (matrix-entries r)])
                     (if ($false? val)
                         (make-list (expt usize (sub1 (length decls))) #f)
                         (begin
                           (hash-set! relations v (singleton-matrix universe i))
                           (begin0
                             (comprehension* (cdr decls) (and pre val))
                             (hash-remove! relations v)))))))))
  (matrix (comprehension* decls #t)))


(: interpret-formula-short-circuit : (C→ Any Any Any Any Any Bool))
(define (interpret-formula-short-circuit rec args op iden !iden)
  (let loop ([args args] [val iden])
    (if (null? args)
        val
        (let ([v (op val (rec (car args)))])
          (if ($equal? v !iden)
              !iden
              (loop (cdr args) v))))))

(: interpret-formula-op : (C→ CUniverse RelationHash Any Any Cache Bool))
(define (interpret-formula-op universe relations op args cache)
  (define rec (curryr interpret-rec universe relations cache))
  (match op
    [(? node/formula/op/&&?)
     (interpret-formula-short-circuit rec args && #t #f)]
    [(? node/formula/op/||?)
     (interpret-formula-short-circuit rec args || #f #t)]
    [(? node/formula/op/=>?)
     (or (not (rec (first args))) (rec (second args)))]
    [_ (let ([args ($map rec args)])
         (match op
           [(? node/formula/op/in?)
            (let ([A (first args)] [B (second args)])
              (matrix/subset? universe A B))]
           [(? node/formula/op/=?)
            (let ([A (first args)] [B (second args)])
              (matrix/equal? universe A B))]
           [(? node/formula/op/!?)
            (not (first args))]))]))


; quantifier: 'all or 'some
; decls: (listof (list ast/node/relation matrix?)) binds the domains of the quantified variables
; f: the predicate
(: interpret-quantifier : (C→ CUniverse RelationHash Any Any Any Any Matrix))
(define (interpret-quantifier universe relations quantifier decls f cache)
  (define usize (universe-size universe))
  (define (evaluate-quantifier op conn)
    (define (rec decls)
      (if (null? decls)
          (interpret-rec f universe relations (and cache (hash-copy cache)))
          (match-let ([(list v r) (car decls)])
            (apply op (for/list ([i usize][val (matrix-entries r)] #:unless ($false? val))
                        (hash-set! relations v (singleton-matrix universe i))
                        (begin0
                          (conn val (rec (cdr decls)))
                          (hash-remove! relations v)))))))
    (rec decls))
  ;; TODO: This should not be (case .... ['sym ....]).
  (case quantifier
    ['all  (evaluate-quantifier && =>)]
    ['some (evaluate-quantifier || &&)]))


(: interpret-multiplicity : (C→ CUniverse CSymbol Matrix Bool))
(define (interpret-multiplicity universe mult expr)
  (match mult
    ['one  (matrix/one? universe expr)]
    ['no   (not (matrix/some? universe expr))]
    ['some (matrix/some? universe expr)]
    ['lone (or (not (matrix/some? universe expr)) (matrix/one? universe expr))]))
