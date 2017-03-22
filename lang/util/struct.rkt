#lang turnstile

(provide struct)

(require racket/splicing
         (except-in turnstile/examples/rosette/rosette2
                    define λ #%app
                    C→ ~C→
                    Ccase-> ~Ccase->)
         (prefix-in ro: (only-in rosette/safe struct))
         "extra-types.rkt"
         "define-lambda-app.rkt")
(module+ test
  (require turnstile/examples/tests/rackunit-typechecking))

(begin-for-syntax
  (define (add-pred stx pred)
    (set-stx-prop/preserved stx 'pred pred))
  (define (get-pred stx)
    (syntax-property stx 'pred)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])

(begin-for-syntax
  (define struct-transformer-binding 'struct-transformer-binding)
  (define struct-instance-type 'struct-instance-type)
  (define struct-field-types 'struct-field-types)
  (define-syntax-class super
    [pattern super:id
      #:with [id-:id τ_inst [τ_fld ...]]
      (let ([super (local-expand #'super 'expression '())])
        (list (syntax-property super struct-transformer-binding)
              (syntax-property super struct-instance-type)
              (syntax-property super struct-field-types)))])
  (define-splicing-syntax-class struct-options
    [pattern (~seq #:transparent refl:struct-opt-reflection-name)
      #:with [opt- ...] #'[#:transparent refl.opt- ...]])
  (define-splicing-syntax-class struct-opt-reflection-name
    [pattern (~seq)
      #:with [opt- ...] #'[]]
    [pattern (~seq #:reflection-name
                   (~and sym-expr:expr
                         ;; TODO: use a Turnstile pattern-expander
                         ;; for typechecking this
                         #; (~⊢ sym-expr ≫ sym-expr- ⇐ CSymbol)
                         (~parse sym-expr- (expand/df #'sym-expr))
                         (~do (define given (typeof #'sym-expr-))
                              (define expected ((current-type-eval) #'CSymbol)))
                         (~fail #:unless (typecheck? given expected)
                                (typecheck-fail-msg/1 expected given #'sym-expr))))
      #:with [opt- ...] #'[#:reflection-name sym-expr-]])
  )

(define-syntax-parser struct
  #:datum-literals [:]
  [(_ name:id ([field:id : τ:type] ...) #:type-name Name:id opts:struct-options)
   #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
   #:with name? (format-id #'name "~a?" #'name #:source #'name)
   #:with [name-field ...]
   (for/list ([field (in-list (syntax->list #'[field ...]))])
     (format-id #'name "~a-~a" #'name field))
   #:with [name* internal-name name?* name-field* ...]
   (generate-temporaries #'[name name name? field ...])
   #'(begin-
       (define-base-type CName)
       (define-named-type-alias Name (add-predm (U CName) name?))
       (splicing-local [(ro:struct name [field ...] opts.opt- ...)]
         (define- name* name)
         (define- name?* name?)
         (define- name-field* name-field)
         ...
         (define-syntax internal-name (make-rename-transformer #'name)))
       (define-struct-name name name* internal-name CName [τ ...])
       (define name?
         (unsafe-assign-type name?* : (C→ Any Bool)))
       (define name-field
         (unsafe-assign-type name-field* : (Ccase-> (C→ CName τ)
                                                    (C→ Name (U τ)))))
       ...)]
  [(_ name:id super:super ([field:id : τ:type] ...) opts:struct-options)
   #:with name? (format-id #'name "~a?" #'name #:source #'name)
   #:with [name-field ...]
   (for/list ([field (in-list (syntax->list #'[field ...]))])
     (format-id #'name "~a-~a" #'name field))
   #:with [name* internal-name name?* name-field* ...]
   (generate-temporaries #'[name name name? field ...])
   #'(begin-
       (splicing-local [(ro:struct name super.id- [field ...] opts.opt- ...)]
         (define- name* name)
         (define- name?* name?)
         (define- name-field* name-field)
         ...
         (define-syntax internal-name (make-rename-transformer #'name)))
       (define-struct-name name name* internal-name super.τ_inst [super.τ_fld ... τ ...])
       (define name?
         (unsafe-assign-type name?* : (C→ Any Bool)))
       (define name-field
         (unsafe-assign-type name-field* :
                             (Ccase-> (C→ super.τ_inst τ)
                                      (C→ (U super.τ_inst) (U τ)))))
       ...)]
  )

(define-syntax-parser define-struct-name
  [(_ name constructor untyped-transformer type [field-type ...])
   #'(define-syntax name
       (make-variable-like-transformer
        (set-stx-prop/preserved
         (set-stx-prop/preserved
          (set-stx-prop/preserved
           (⊢ constructor : (C→ field-type ... type))
           struct-transformer-binding
           (quote-syntax untyped-transformer))
          struct-instance-type
          (quote-syntax type))
         struct-field-types
         (list (quote-syntax field-type) ...))))])

;; ----------------------------------------------------------------------------

(module+ test
  (struct a () #:type-name A #:transparent)
  (struct b () #:type-name B #:transparent)
  (struct c () #:type-name C #:transparent)
  (struct d () #:type-name D #:transparent)
  (struct e () #:type-name E #:transparent)
  (struct abc ([a : A] [b : B] [c : C]) #:type-name ABC #:transparent)

  (check-type (a) : A -> (a))
  (check-type (b) : B -> (b))
  (check-type (c) : C -> (c))
  (check-type (d) : D -> (d))
  (check-type (e) : E -> (e))
  (check-type (abc (a) (b) (c)) : ABC -> (abc (a) (b) (c)))
  (typecheck-fail (abc (a) 3 (c))
    #:with-msg
    "expected B, given PosInt\n *expression: 3"
    #;"expected: *A, B, C\n *given: *CA, PosInt, CC\n *expressions: \\(a\\), 3, \\(c\\)")

  ;; predicates
  (check-type (a? (a)) : Bool -> #true)
  (check-type (a? (b)) : Bool -> #false)
  (check-type (a? (abc (a) (b) (c))) : Bool -> #false)
  (check-type (abc? (abc (a) (b) (c))) : Bool -> #true)

  ;; inheritance
  ;; This doesn't actually define a new type, it always uses
  ;; the super type. So type of (abcde ...) is just ABC.
  (struct abcde abc ([d : D] [e : E]) #:transparent)

  (check-type (abcde (a) (b) (c) (d) (e)) : ABC
              -> (abcde (a) (b) (c) (d) (e)))
  (typecheck-fail (abcde (a) (b) (c) 3 (e))
    #:with-msg
    "expected D, given PosInt\n *expression: 3"
    #;"expected: *A, B, C, D, E\n *given: *CA, CB, CC, PosInt, CE\n *expressions: \\(a\\), \\(b\\), \\(c\\), 3, \\(e\\)")

  ;; TODO: it should be an instance of ABCDE
  ;;       and still an instance of ABC
  #;(check-type (abcde (a) (b) (c) (d) (e)) : ABCDE
              -> (abcde (a) (b) (c) (d) (e)))
  #;(check-type (abcde (a) (b) (c) (d) (e)) : ABC
              -> (abcde (a) (b) (c) (d) (e)))

  ;; inheritance and predicates
  (check-type (abc? (abc (a) (b) (c))) : Bool -> #true)
  (check-type (abcde? (abcde (a) (b) (c) (d) (e))) : Bool -> #true)
  (check-type (abc? (abcde (a) (b) (c) (d) (e))) : Bool -> #true)
  (check-type (a? (abcde (a) (b) (c) (d) (e))) : Bool -> #false)
  (check-type (abcde? (abc (a) (b) (c))) : Bool -> #false)
  )
