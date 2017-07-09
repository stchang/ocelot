#lang typed/rosette

(require "../lang/util/extra-types.rkt"
         "../lang/util/extra-forms.rkt"
         "../lang/bounds.rkt" "../lang/universe.rkt" "matrix.rkt"
         (only-in "../lang/ast.rkt" CNode/Expr relation-arity)
         (prefix-in $ racket))
(provide (all-defined-out))

; An interpretation is a universe and an association list of (relation, matrix)
; pairs
(struct interpretation
  ([universe : CUniverse]
   [entries : (CListof (CPair CNode/Expr CMatrix))])
  #:transparent)

; receives an ast/node/relation and an uninterpreted bound

; Create an interpretation of the given bounds
(: instantiate-bounds : (C→ CBounds CInterpretation))
(define (instantiate-bounds bounds)
  (let ([U (bounds-universe bounds)])
    (interpretation
      U
      (for/list ([bnd (in-list (bounds-entries bounds))])
        (let* ([rel (bound-relation bnd)]
               [size (expt (universe-size U) (relation-arity rel))]
               [mat
                (cond [(equal? (bound-lower bnd) (bound-upper bnd))
                       (let ([members
                              (for/list ([tup (in-list (bound-upper bnd))])
                                (tuple->idx U tup))])
                         (matrix (for/list ([i (in-range size)])
                                   (set-member? members i))))]
                      [else
                       (let ([lower
                              (for/list ([tup (in-list (bound-lower bnd))])
                                (tuple->idx U tup))]
                             [upper
                              (for/list ([tup (in-list (bound-upper bnd))])
                                (tuple->idx U tup))])
                         (matrix (for/list ([i (in-range size)])
                                   (cond [(set-member? lower i) #t]
                                         [(set-member? upper i)
                                          (let-symbolic* [r boolean?]
                                            r)]
                                         [else #f]))))])])
          (pair rel mat))))))

(: interpretation-union :
   (C→* [] [] #:rest (CListof CInterpretation) CInterpretation))
(define (interpretation-union . interps)
  (let ([U (interpretation-universe (first interps))])
    (interpretation
      U
      (for*/list ([i : CInterpretation (in-list interps)]
                  [e : (CPair CNode/Expr CMatrix) (in-list (interpretation-entries i))])
        e))))

(: interpretation->relations : (C→ CInterpretation Any))
(define (interpretation->relations interp)
  (match interp
    [(interpretation U entries)
     (for/hash ([p (in-list entries)])
       (match p
         [(pair rel mat)
          (let* ([contents (matrix-entries mat)]
                 [arity (matrix-entries-arity U contents)])
            (if (andmap concrete-boolean? contents)
                (tup rel
                     (for/list ([x (in-list contents)]
                                [i (in-naturals)]
                                #:when x)
                       (idx->tuple U arity i)))
                (error 'interpretation->relations
                  "matrix must be fully concrete\n  relation: ~v\n  matrix: ~v"
                  rel mat)))]))]))
