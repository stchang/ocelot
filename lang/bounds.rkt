#lang typed/rosette

(require "../lang/util/struct.rkt"
         "../lang/util/extra-forms.rkt"
         (only-in "universe.rkt" CUniverse)
         (only-in "ast.rkt" CNode/Expr relation-arity))

(provide (all-defined-out))

(require (only-in racket/base begin-for-syntax) (for-syntax racket/base syntax/parse/debug))
(begin-for-syntax (debug-syntax-parse!))

; A bound is a relation and two lists of tuples `lower` and `upper`.
(struct bound
  ([relation : CNode/Expr]
   [lower : (CListof (CListof CSymbol))]
   [upper : (CListof (CListof CSymbol))])
  #:transparent)
; A bounds object is a universe and a collection of bound? instances.
(struct bounds
  ([universe : CUniverse]
   [entries : (CListof CBound)])
  #:transparent)

; Error-checking constructors for bounds
(: make-bound : (C→ CNode/Expr (CListof (CListof CSymbol)) (CListof (CListof CSymbol)) CBound))
(define (make-bound relation lower upper)
  (for ([t (in-list lower)])
    (unless (and (list? t) (= (length t) (relation-arity relation)))
      (raise-arguments-error 'make-bound "bounds must contain tuples" "lower" t)))
  (for ([t (in-list upper)])
    (unless (and (list? t) (= (length t) (relation-arity relation)))
      (raise-arguments-error 'make-bound "bounds must contain tuples" "upper" t)))
  (bound relation lower upper))

(: make-exact-bound : (C→ CNode/Expr (CListof (CListof CSymbol)) CBound))
(define (make-exact-bound relation contents)
  (make-bound relation contents contents))

(: make-upper-bound : (C→ CNode/Expr (CListof (CListof CSymbol)) CBound))
(define (make-upper-bound relation contents)
  (make-bound relation '() contents))

(: make-product-bound : (C→* [CNode/Expr (CListof CSymbol)] []
                             #:rest (CListof (CListof CSymbol))
                             CBound))
(define (make-product-bound relation col1 . columns)
  (make-bound relation '()
              (ann (cartesian-product* (ann (cons col1 columns) : (CListof (CListof CSymbol))))
                   : (CListof (CListof CSymbol)))))

; Get the upper bound for a relation r in a bounds? object
(: get-upper-bound : (C→ CBounds CNode/Expr (U (CListof (CListof CSymbol)) Bool)))
(define (get-upper-bound bnds r)
  (for/or ([b (in-list (bounds-entries bnds))])
    (if (equal? (bound-relation b) r)
        (bound-upper b)
        #false)))

; get a list of all relations bound by a bounds? object
(: bounds-variables : (C→ CBounds (CListof CNode/Expr)))
(define (bounds-variables bnds)
  (for/list ([b (in-list (bounds-entries bnds))]) (bound-relation b)))

; Combine several sets of bounds, which must be mutually disjoint and share the
; same universe
(: bounds-union : (C→* [] [] #:rest (CListof CBounds) CBounds))
(define (bounds-union . lbnds)
  (let ([U (bounds-universe (car lbnds))])
    (bounds U (for*/list ([bnds : CBounds (in-list lbnds)]
                          [bnd : CBound (in-list (bounds-entries bnds))])
                bnd))))
