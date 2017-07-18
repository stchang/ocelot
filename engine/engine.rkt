#lang typed/rosette

(require (only-in typed/rosette/base-forms unsafe-assign-type)
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

(define-type-alias ExprCacheHash
  (CHashTable CNode/Expr CMatrix))
(define-type-alias FormulaCacheHash
  (CHashTable CNode/Formula Bool))
(define-type-alias ExprCache
  (CU ExprCacheHash CFalse))
(define-type-alias FormulaCache
  (CU FormulaCacheHash CFalse))

(: expr-cache-copy : (C→ ExprCache ExprCache))
(define (expr-cache-copy expr-cache)
  (and (not (false? expr-cache)) (hash-copy expr-cache)))

(: formula-cache-copy : (C→ FormulaCache FormulaCache))
(define (formula-cache-copy formula-cache)
  (and (not (false? formula-cache)) (hash-copy formula-cache)))

;; ------------------------------------------------------------------------

(: interpret : (Ccase-> (C→ CNode/Expr CBounds CMatrix)
                        (C→ CNode/Formula CBounds Bool)))
(define (interpret formula bounds)
  (let ([interp (instantiate-bounds bounds)])
    (if (node/expr? formula)
        (interpret* formula interp)
        (interpret* formula interp))))

(: interpret* :
   (Ccase-> (C→ CNode/Expr CInterpretation [#:cache? CBool] CMatrix)
            (C→ CNode/Formula CInterpretation [#:cache? CBool] Bool)))
(define (interpret* formula interp #:cache? [cache? #f])
  (match interp
    [(interpretation universe entries)
     (let ([relations (make-hash entries)])
       (if (node/expr? formula)
           (interpret-rec formula
                          universe
                          relations
                          (if cache? (ann (make-hash) : ExprCacheHash) #f)
                          (if cache? (ann (make-hash) : FormulaCacheHash) #f))
           (interpret-rec formula
                          universe
                          relations
                          (if cache? (ann (make-hash) : ExprCacheHash) #f)
                          (if cache? (ann (make-hash) : FormulaCacheHash) #f))))]))

;; the hash table is mutable!
(: interpret-rec :
   (Ccase->
    (C→ CNode/Expr CUniverse RelationHash ExprCache FormulaCache CMatrix)
    (C→ CNode/Formula CUniverse RelationHash ExprCache FormulaCache Bool)))
(define (interpret-rec formula universe relations expr-cache formula-cache)
  (if (node/expr? formula)
      (if (not (false? expr-cache))
          (hash-ref! expr-cache
                     formula
                     (λ () (interpret-body formula universe relations expr-cache formula-cache)))
          (interpret-body formula universe relations expr-cache formula-cache))
      (if (not (false? formula-cache))
          (hash-ref! formula-cache
                     formula
                     (λ () (interpret-body formula universe relations expr-cache formula-cache)))
          (interpret-body formula universe relations expr-cache formula-cache))))

(: interpret-body :
   (Ccase->
    (C→ CNode/Expr CUniverse RelationHash ExprCache FormulaCache CMatrix)
    (C→ CNode/Formula CUniverse RelationHash ExprCache FormulaCache Bool)))
(define (interpret-body formula universe relations expr-cache formula-cache)
  (match formula
    [(node/expr/op arity args)
     (let ([args* (for/list ([a (in-list args)])
                    (interpret-rec a universe relations expr-cache formula-cache))])
       (interpret-expr-op universe
                          formula
                          args*))]
    [(node/expr/relation arity name)
     (hash-ref relations
               formula
       (λ () (error 'interpret "unbound relation ~a" formula)))]
    [(node/expr/constant arity type)
     (interpret-constant universe type)]
    [(node/expr/comprehension arity decls f)
     (let ([decls* (for/list ([d (in-list decls)])
                     (pair (car d) (interpret-rec (cdr d) universe relations expr-cache formula-cache)))])
       (interpret-comprehension universe relations decls* f expr-cache formula-cache))]
    [(node/formula/op args)
     (interpret-formula-op universe relations formula args expr-cache formula-cache)]
    [(node/formula/quantified quantifier decls f)
     (let ([decls* (for/list ([d (in-list decls)])
                     (pair (car d) (interpret-rec (cdr d) universe relations expr-cache formula-cache)))])
       (interpret-quantifier universe relations quantifier decls* f expr-cache formula-cache))]
    [(node/formula/multiplicity mult expr)
     (let ([expr* (interpret-rec expr universe relations expr-cache formula-cache)])
       (interpret-multiplicity universe mult expr*))]))


(: interpret-constant : (C→ CUniverse CSymbol CMatrix))
(define (interpret-constant universe type)
  (match type
    ['none (matrix (make-list (universe-size universe) #f))]
    ['univ (matrix (make-list (universe-size universe) #t))]
    ['iden (let ([size (universe-size universe)])
             (matrix (for*/list ([i : CNat (in-range size)]
                                 [j : CNat (in-range size)])
                       (= i j))))]))


(: interpret-expr-op : (C→ CUniverse CNode/Expr (CListof CMatrix) CMatrix))
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


(: interpret-comprehension :
   (C→ CUniverse
       RelationHash
       (CListof (CPair CNode/Expr CMatrix))
       CNode/Formula
       ExprCache
       FormulaCache
       CMatrix))
(define (interpret-comprehension universe relations decls f expr-cache formula-cache)
  (let ([usize (universe-size universe)])
    (letrec
        ([[comprehension* : (C→ (CListof (CPair CNode/Expr CMatrix))
                                Bool
                                RelationHash
                                (CListof Bool))]
          (λ (decls pre relations)
            (if (null? decls)
                (list (and pre
                           (interpret-rec f universe relations
                                          (expr-cache-copy expr-cache)
                                          (formula-cache-copy formula-cache))))
                (match-let ([(pair v r) (car decls)])
                  (append* (for/list ([i (in-range usize)]
                                      [val (in-list (matrix-entries r))])
                             (if ($false? val)
                                 (make-list (expt usize (length (cdr decls)))
                                            #f)
                                 (begin
                                   (hash-set! relations v (singleton-matrix universe i))
                                   (begin0
                                     (comprehension* (cdr decls) (and pre val) relations)
                                     (hash-remove! relations v)))))))))])
      (matrix (comprehension* decls #t relations)))))


(: interpret-formula-short-circuit :
   (C→ (C→ CNode/Formula Bool)
       (CListof CNode/Formula)
       (C→ Bool Bool Bool)
       CBool
       CBool
       Bool))
(define (interpret-formula-short-circuit rec args op iden !iden)
  (let loop ([args : (CListof CNode/Formula) args] [val : Bool iden])
    (if (null? args)
        val
        (let ([v (op val (rec (car args)))])
          (if ($equal? v !iden)
              !iden
              (loop (cdr args) v))))))

(: interpret-formula-op :
   (C→ CUniverse RelationHash
       CNode/Formula
       (CListof (CU CNode/Formula CNode/Expr))
       ExprCache
       FormulaCache
       Bool))
(define (interpret-formula-op universe relations op args expr-cache formula-cache)
  (let ([rec  (partialr interpret-rec universe relations expr-cache formula-cache)])
    (match op
      [(? node/formula/op/&&?)
       (let ([args (unsafe-assign-type args : (CListof CNode/Formula))])
         (interpret-formula-short-circuit rec args && #t #f))]
      [(? node/formula/op/||?)
       (let ([args (unsafe-assign-type args : (CListof CNode/Formula))])
         (interpret-formula-short-circuit rec args || #f #t))]
      [(? node/formula/op/=>?)
       (let ([args (unsafe-assign-type args : (CListof CNode/Formula))])
         (or (not (rec (first args))) (rec (second args))))]
      [_ (let ([args (for/list ([arg (in-list args)])
                       (if (node/expr? arg)
                           (rec arg)
                           (rec arg)))])
           (match op
             [(? node/formula/op/in?)
              (let ([A (first args)] [B (second args)])
                (if (and (matrix? A) (matrix? B))
                    (matrix/subset? universe A B)
                    (error 'interpret-in "bad")))]
             [(? node/formula/op/=?)
              (let ([A (first args)] [B (second args)])
                (if (and (matrix? A) (matrix? B))
                    (matrix/equal? universe A B)
                    (error 'interpret-in "bad")))]
             [(? node/formula/op/!?)
              (not (first args))]))])))


; quantifier: 'all or 'some
; decls: (listof (cons ast/node/relation matrix?)) binds the domains of the quantified variables
; f: the predicate
(: interpret-quantifier :
   (C→ CUniverse
       RelationHash
       Any
       (CListof (CPair CNode/Expr CMatrix))
       CNode/Formula
       ExprCache
       FormulaCache
       Bool))
(define (interpret-quantifier universe relations quantifier decls f expr-cache formula-cache)
  (let ([usize (universe-size universe)])
    (letrec
        ([(evaluate-quantifier : (C→ (C→* [] [] #:rest (CListof Bool) Bool)
                                     (C→ Bool Bool Bool)
                                     RelationHash
                                     Bool))
          (λ (op conn relations)
            (letrec
                ([(rec : (C→ (CListof (CPair CNode/Expr CMatrix)) RelationHash Bool))
                  (λ (decls relations)
                    (if (null? decls)
                        (interpret-rec f universe relations
                                       (expr-cache-copy expr-cache)
                                       (formula-cache-copy formula-cache))
                        (match-let ([(pair v r) (car decls)])
                          (apply
                           op
                           (for/list ([i (in-range usize)]
                                      [val (in-list (matrix-entries r))]
                                      #:unless ($false? val))
                             (begin
                               (hash-set! relations v (singleton-matrix universe i))
                               (begin0
                                 (conn val (rec (cdr decls) relations))
                                 (hash-remove! relations v))))))))])
              (rec decls relations)))])
      (match quantifier
        ['all  (evaluate-quantifier && => relations)]
        ['some (evaluate-quantifier || && relations)]))))


(: interpret-multiplicity : (C→ CUniverse CSymbol CMatrix Bool))
(define (interpret-multiplicity universe mult expr)
  (match mult
    ['one  (matrix/one? universe expr)]
    ['no   (not (matrix/some? universe expr))]
    ['some (matrix/some? universe expr)]
    ['lone (or (not (matrix/some? universe expr)) (matrix/one? universe expr))]))

