#lang turnstile

(provide CVoid Void
         COutputPort
         CHashof
         CSequenceof
         C→ C→* Ccase->
         C→*/internal- MandArgs- OptKws- KwArg- RestArg- NoRestArg-
         (for-syntax ~CHashof
                     ~CSequenceof
                     ~C→ ~C→*/internal ~Ccase->
                     C→/normal? C→*/internal?
                     ~MandArgs ~OptKws ~KwArg ~RestArg ~NoRestArg
                     ~C×
                     ~CListof))

(require (only-in turnstile/examples/stlc+tup
                  [~× ~C×])
         (only-in turnstile/examples/stlc+union+case
                  [case-> Ccase->/internal] [~case-> ~Ccase->])
         (only-in turnstile/examples/rosette/rosette2
                  define-named-type-alias
                  U
                  CListof ~CListof
                  CSymbol
                  [C→ C→/normal] [~C→ ~C→/normal] [C→? C→/normal?]))

(begin-for-syntax
  (define (add-pred stx pred)
    (set-stx-prop/preserved stx 'pred pred))
  (define (get-pred stx)
    (syntax-property stx 'pred)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])

(define-base-type CVoid)
(define-named-type-alias Void (add-predm (U CVoid) void?))

(define-base-type COutputPort)

(define-type-constructor CHashof #:arity = 2)
(define-type-constructor CSequenceof #:arity = 1)

(begin-for-syntax
  (begin-for-syntax
    (define-syntax-class expr*
      [pattern (~and :expr (~not [:keyword . _]))]))
  (define-syntax-class expr*
    [pattern (~and :expr (~not [:keyword . _]))]))

(define-internal-type-constructor C→*/internal) ; #:arity = 4
(define-internal-type-constructor MandArgs) ; #:arity >= 0
(define-internal-type-constructor OptKws) ; #:arity >= 1

(define-internal-type-constructor NoRestArg) ; #:arity = 0
(define-internal-type-constructor RestArg) ; #:arity = 1

(define-internal-type-constructor KwArg) ; #:arity = 2

;; (C→* mandatory optional output)
;; (C→* mandatory optional #:rest rest output)
;;   mandatory ::= [τ ...]
;;    optional ::= [kw/τ ...]
;;        rest ::= τ
;;      output ::= τ
;;       kw/τ ::= kw τ
(define-typed-syntax C→*
  ;; For this special case, expand to C→/normal instead
  [(_ [τ_in:expr* ...] [] τ_out:expr*) ≫
   --------
   [≻ (C→/normal τ_in ... τ_out)]]
  [(_ [τ_in:expr* ...] [(~seq kw:keyword τ_kw:expr*) ...+] τ_out:expr*) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (NoRestArg-)
                     τ_out-)
      ⇒ :: #%type]]
  [(_ [τ_in:expr* ...] [(~seq kw:keyword τ_kw:expr*) ...] #:rest τ_rst τ_out:expr*) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_rst ≫ τ_rst- ⇐ :: #%type]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (RestArg- τ_rst-)
                     τ_out-)
      ⇒ :: #%type]])

(define-typed-syntax C→
  [(_ τ_in:expr* ... [kw:keyword τ_kw:expr*] ... τ_out:expr*) ≫
   #:with [[kw/τ ...] ...] #'[[kw τ_kw] ...]
   --------
   [≻ (C→* [τ_in ...] [kw/τ ... ...] τ_out)]])

(begin-for-syntax
  (define-syntax ~C→
    (pattern-expander
     (syntax-parser
       [(_ pat_in:expr* ... pat_out:expr*)
        #'(~C→/normal pat_in ... pat_out)]))))

(define-syntax Ccase->
  (syntax-parser
    [(_ . tys)
     #:do [(define (concrete-function-type? τ)
             (or (C→/normal? τ) (C→*/internal? τ)))]
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete-function-type? #'tys+)
                   "Ccase-> require concrete function types"
     #'(Ccase->/internal . tys+)]))

(define-typed-syntax m
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ _]
   #:do [(println #'e-)]
   -------
   [⊢ (void-) ⇒ CVoid]])
