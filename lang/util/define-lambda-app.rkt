#lang turnstile

(provide define λ apply
         (rename-out [app #%app])
         unsafe-assign-type unsafe-define/assign-type)

(require (except-in turnstile/examples/rosette/rosette2
                    #%app
                    C→ ~C→
                    Ccase-> ~Ccase->)
         (prefix-in ro: (only-in rosette/safe define λ #%app))
         "extra-types.rkt")

(begin-for-syntax
  ;; split-at* : [Listof A] [Listof Natural] -> [Listof [Listof A]]
  (define (split-at* lst lengths)
    (cond [(empty? lengths) (list lst)]
          [else
           (define-values [fst rst]
             (split-at lst (first lengths)))
           (cons fst (split-at* rst (rest lengths)))]))
  )

;; ----------------------------------------------------------------------------

;; Define and Lambda

;; This new version of define handles keyword arguments,
;; and also uses make-variable-like-transformer so that
;; types are preserved accross modules.

(define-typed-syntax define
  #:datum-literals [: →]
  [(_ x:id : τ e:expr) ≫
   #:with x- (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax- x (make-variable-like-transformer (⊢ x- : τ)))
        (ro:define x- (ann e : τ)))]]
  [(_ x:id e:expr) ≫
   #:with x- (generate-temporary #'x)
   [⊢ e ≫ e- ⇒ τ]
   --------
   [≻ (begin-
        (define-syntax- x (make-variable-like-transformer (⊢ x- : τ)))
        (ro:define x- e-))]]
  ;; function with no rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ...) → τ_out
      body ...+) ≫
   #:with f- (generate-temporary #'f)
   #:with [[kw-arg ...] ...] #'[[kw [y e_def]] ...]
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ...)
                  (ann body* : τ_out)))
   #:with lam* (syntax/loc this-syntax
                 (λ (x ... kw-arg ... ...) body*))
   --------
   [≻ (define f : (C→ τ_in ... [kw τ_kw] ... τ_out)
        lam)]]
  ;; function with rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ... . [rst:id : τ_rst]) → τ_out
      body ...+) ≫
   #:with f- (generate-temporary #'f)
   #:with [[kw/τ ...] ...] #'[[kw τ_kw] ...]
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ... . [rst : τ_rst])
                  (ann body* : τ_out)))
   --------
   [≻ (define f : (C→* [τ_in ...] [kw/τ ... ...] #:rest τ_rst τ_out)
        lam)]])

;; This new version of λ handles keyword arguments.

(define-typed-syntax λ
  #:datum-literals [:]
  ;; no expected type
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (ro:λ (x- ...) e-) ⇒ (C→ τ_in.norm ... τ_out)]]
  ;; need expected type
  [(_ (x:id ...) e) ⇐ (~C→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (ro:λ (x- ...) e-)]]
  [(_ (x:id ... (~seq kw:keyword [y:id e_def:expr]) ...) body)
   ⇐ (~C→*/internal (~MandArgs τ_in ...) (~OptKws (~KwArg (_ kw*) τ_kw) ...) (~NoRestArg) τ_out) ≫
   #:fail-unless (equal? (syntax->datum #'[kw ...])
                         (syntax->datum #'[kw* ...]))
   (format "keywords don't match, expected ~a, given ~a"
           (syntax->datum #'[kw* ...])
           (syntax->datum #'[kw ...]))
   [⊢ [e_def ≫ e_def- ⇐ τ_kw] ...]
   [[x ≫ x-- : τ_in] ... [y ≫ y-- : τ_kw] ... ⊢ body ≫ body- ⇐ τ_out]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   ---------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)]]
  [(_ (x:id ... . rst:id) e)
   ⇐ (~C→*/internal (~MandArgs τ_in ...) (~OptKws) (~RestArg τ_rst) τ_out) ≫
   [[x ≫ x-- : τ_in] ... [rst ≫ rst-- : τ_rst]
    ⊢ e ≫ e- ⇐ τ_out]
   #:with [[x- ...] [rst-]] (split-at* (stx->list #'[x-- ... rst--])
                                       (list (length (stx->list #'[x ...]))))
   ---------
   [⊢ (ro:λ (x- ... . rst-) e-)]]
  ;; no expected type, keyword arguments
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ...+)
      body) ≫
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... ⊢ body ≫ body- ⇒ τ_out]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)
      ⇒ (C→ τ_in ... [kw τ_kw] ... τ_out)]]
  ;; no expected type, rest argument
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ... . [rst:id : τ_rst:type])
      body) ≫
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... [rst ≫ rst-- : τ_rst.norm]
    ⊢ body ≫ body- ⇒ τ_out]
   #:with [[x- ...] [y- ...] [rst-]]
   (split-at* (stx->list #'[x-- ... y-- ... rst--])
              (list (length (stx->list #'[x ...]))
                    (length (stx->list #'[y ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   #:with [[kw-τ ...] ...] #'[[kw τ_kw.norm] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ... . rst-) body-)
      ⇒ (C→* [τ_in.norm ...] [kw-τ ... ...] #:rest τ_rst.norm τ_out)]]
  )

;; ----------------------------------------------------------------------------

;; Function Application

(define-typed-syntax app
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   [⊢ f ≫ f- ⇒ (~and (~or (~C→ _ ...) (~C→*/internal _ ...)) ~! τ_f)]
   #:with (~C→*/internal (~MandArgs τ_a ...)
                         (~OptKws (~KwArg (_ kw*) τ_kw*) ...)
                         (~NoRestArg)
                         τ_out)
   (coerce-to-C→* #'τ_f)
   #:do [(define kws/τs*
           (for/list ([kw* (in-list (syntax->datum #'[kw* ...]))]
                      [τ* (in-list (syntax->list #'[τ_kw* ...]))])
             (list kw* τ*)))]
   #:with [τ_b ...]
   (for/list ([kw (in-list (syntax->list #'[kw ...]))])
     (define p (assoc (syntax-e kw) kws/τs*))
     (unless p (raise-syntax-error #f "keyword not in domain of function" kw))
     (second p))
   [⊢ [a ≫ a- ⇐ τ_a] ...]
   [⊢ [b ≫ b- ⇐ τ_b] ...]
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ τ_out]]
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! τ_f ...)]
   [⊢ [a ≫ a- ⇒ τ_a] ...]
   [⊢ [b ≫ b- ⇒ τ_b] ...]
   #:with τ_out
   (for/or ([τ_f (in-list (stx-map coerce-to-C→* #'[τ_f ...]))])
     (syntax-parse τ_f
       [(~C→*/internal (~MandArgs τ_a* ...)
                       (~OptKws (~KwArg (_ kw*) τ_kw*) ...)
                       (~NoRestArg)
                       τ_out)
        (define kws/τs*
          (for/list ([kw (in-list (syntax->datum #'[kw* ...]))]
                     [τ (in-list (syntax->list #'[τ_kw* ...]))])
            (list kw τ)))
        (and (typechecks? #'[τ_a ...] #'[τ_a* ...])
             (for/and ([kw (in-list (syntax->datum #'[kw ...]))]
                       [b (in-list (syntax->list #'[b ...]))])
               (define p (assoc kw kws/τs*))
               (and p
                    (typecheck? b (second p))))
             #'τ_out)]
       [_ #false]))
   #:fail-unless (syntax-e #'τ_out) "none of the cases matched"
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ τ_out]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~CU* τ_f ...)]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ (CU τ_out ...)]]
  [(_ e_fn e_arg ...) ≫
   [⊢ [e_fn ≫ e_fn- ⇒ : (~U* τ_f ...)]]
   #:with e_fn/progsrc- (replace-stx-loc #'e_fn- #'e_fn)
   [⊢ [e_arg ≫ e_arg- ⇒ : τ_arg] ...]
   #:with (f a ...) (generate-temporaries #'(e_fn e_arg ...))
   [([f ≫ _ : τ_f] [a ≫ _ : τ_arg] ...)
    ⊢ [(app f a ...) ≫ _ ⇒ : τ_out]]
   ...
   --------
   [⊢ (ro:#%app e_fn/progsrc- e_arg- ...) ⇒ (U τ_out ...)]])

(begin-for-syntax
  (define (coerce-to-C→* τ)
    (cond [(C→*/internal? τ) τ]
          [(C→/normal? τ)
           (syntax-parse τ
             [(~C→ τ_in ... τ_out)
              ((current-type-eval)
               #'(C→*/internal- (MandArgs- τ_in ...)
                                (OptKws-)
                                (NoRestArg-)
                                τ_out))])]
          [else
           (error 'coerce-to-C→* "not coercable to C→*: ~v" τ)])))

;; ----------------------------------------------------------------------------

;; Apply

;; This version of apply is very limited: it only works with
;; functions that declare a rest argument.

(define-typed-syntax apply
  [(_ f:expr lst:expr) ≫
   [⊢ f ≫ f- ⇒ (~C→*/internal (~MandArgs)
                              (~OptKws)
                              (~RestArg τ_rst)
                              τ_out)]
   [⊢ lst ≫ lst- ⇐ τ_rst]
   --------
   [⊢ (apply- f- lst-) ⇒ τ_out]]
  [(_ f:expr lst:expr) ≫
   [⊢ f ≫ f- ⇒ (~Ccase->
                         _
                         ...
                         (~C→*/internal (~MandArgs)
                                        (~OptKws)
                                        (~RestArg τ_rst)
                                        τ_out)
                         _
                         ...)]
   #:do [(printf "expecting list type ~a\n" #'τ_rst)]
   [⊢ lst ≫ lst- ⇐ τ_rst]
   --------
   [⊢ (apply- f- lst-) ⇒ τ_out]])

;; ----------------------------------------------------------------------------

;; Unsafely assigning types to values

;; unsafe-assign-type doesn't typecheck anything within the expression
(define-typed-syntax unsafe-assign-type
  #:datum-literals [:]
  [(_ e:expr : τ:expr) ≫
   --------
   [⊢ e ⇒ : τ]])

(define-syntax-parser unsafe-define/assign-type
  #:datum-literals [:]
  [(_ x:id : τ:expr e:expr)
   #'(define x (unsafe-assign-type e : τ))])

