#lang typed/rosette

(require (except-in "util/extra-types.rkt" @)
         "util/define-lambda-app.rkt"
         "util/extra-forms.rkt"
         "util/struct.rkt"
         "util/generic-interfaces.rkt"
         "util/require.rkt"
         "util/provide.rkt"
         (prefix-in @ "util/extra-forms.rkt")
         (prefix-in @ (subtract-in typed/rosette
                                   "util/extra-forms.rkt"))
         (prefix-in $ turnstile/examples/stlc+union+case)
         (for-syntax racket/base
                     racket/syntax))

(provide (except-out (all-defined-out) next-name #;@@and #;@@or)
         #;(rename-out [@@and and] [@@or or]))

; Ocelot ASTs are made up of expressions (which evaluate to relations) and
; formulas (which evaluate to booleans).
; All AST structs start with node/. The hierarchy is:
;   * node/expr  -- expressions
;     * node/expr/op  -- simple operators
;       * node/expr/+
;       * node/expr/-
;       * ...
;     * node/expr/comprehension  -- set comprehension
;     * node/expr/relation  -- leaf relation
;     * node/expr/constant  -- relational constant
;   * node/formula  -- formulas
;     * node/formula/op  -- simple operators
;       * node/formula/and
;       * node/formula/or
;       * ...
;     * node/formula/quantified  -- quantified formula
;     * node/formula/multiplicity  -- multiplicity formula

;; EXPRESSIONS -----------------------------------------------------------------

(struct node/expr ([arity : CNat])
  #:type-name Node/Expr
  #:transparent)

;; FORMULAS --------------------------------------------------------------------

(struct node/formula ()
  #:type-name Node/Formula
  #:transparent)

;; ARGUMENT CHECKS -------------------------------------------------------------

(: check-args : (C→ CSymbol (CListof Any) (→ Any Bool)
                    [#:same-arity? Bool]
                    [#:arity Any]
                    [#:min-length CNat]
                    [#:max-length (U Bool Nat)]
                    [#:join? Bool]
                    [#:domain? Bool]
                    [#:range? Bool]
                    CVoid))
(define (check-args op
                    args
                    type?
                    #:same-arity? [same-arity? #f]
                    #:arity [arity #f]
                    #:min-length [min-length 2]
                    #:max-length [max-length #f]
                    #:join? [join? #f]
                    #:domain? [domain? #f]
                    #:range? [range? #f])
  (when (< (length args) min-length)
    (raise-arguments-error op "not enough arguments" "required" min-length "got" (length args)))
  (unless (false? max-length)
    ;; TODO: use occurence typing to get rid of this assert-type
    (when (> (length args) (assert-type max-length : Nat))
      (raise-arguments-error op "too many arguments" "maximum" max-length "got" (length args))))
  (for ([a (in-list args)])
    (unless (type? a)
      (raise-argument-error op (~v type?) a))
    (unless (false? arity)
      (unless (node/expr? a)
        (raise-argument-error op "relation expression" a))
      ;; TODO: use occurence typing instead of assert-type
      (unless (equal? (node/expr-arity (assert-type a : Node/Expr)) arity)
        (raise-argument-error op (format "expression with arity ~v" arity) a))))
  (when same-arity?
    (unless (node/expr? (first args))
      (raise-argument-error op "relation expression" (first args)))
    (let ([arity (node/expr-arity (assert-type (first args) : Node/Expr))])
      (for ([a (in-list args)])
        (unless (node/expr? a)
          (raise-argument-error op "relation expression" a))
        (unless (equal? (node/expr-arity (assert-type a : Node/Expr))
                        arity)
          (raise-arguments-error op "arguments must have same arity"
                                 "got" arity
                                 "and" (node/expr-arity
                                        (assert-type a : Node/Expr)))))))
  (when join?
    (when (<= (apply join-arity (for/list ([a (in-list args)])
                                  (assert-type
                                   (node/expr-arity
                                    (assert-type a : Node/Expr))
                                   : CNat)))
              0)
      (raise-arguments-error op "join would create a relation of arity 0")))
  (when range?
    (unless (node/expr? (second args))
      (raise-argument-error op "relation expression" (second args)))
    (unless (equal? (node/expr-arity (assert-type (second args) : Node/Expr)) 1)
      (raise-arguments-error op "second argument must have arity 1")))
  (when domain?
    (unless (node/expr? (first args))
      (raise-argument-error op "relation expression" (first args)))
    (unless (equal? (node/expr-arity (assert-type (first args) : Node/Expr)) 1)
      (raise-arguments-error op "first argument must have arity 1")))
  (void))

;; -- operators ----------------------------------------------------------------

(struct node/expr/op node/expr ([children : (CListof CNode/Expr)])
  #:use-super-type
  #:transparent)

;; TODO: figure out how to deal with operation arity
(define-syntax (define-expr-op stx)
  (syntax-case stx ()
    [(_ id arity checks ...)
     (with-syntax ([name (format-id #'id "node/expr/op/~a" #'id)])
       (quasisyntax/loc stx
         (splicing-begin
           (struct name node/expr/op () #:use-super-type #:transparent
             #:reflection-name 'id)
           (define id : (C→* [] [] #:rest (CListof CNode/Expr) CNode/Expr)
             (λ e
               (begin
                 (check-args 'id e node/expr? checks ...)
                 (let ([arities (for/list ([a (in-list e)]) (node/expr-arity a))])
                   (name (assert-type (apply arity arities) : CNat) e))))))))]))

(define get-first : (C→* [] [] #:rest (CListof CNat) CNat)
  (λ e (first e)))
(define get-second : (C→* [] [] #:rest (CListof CNat) CNat)
  (λ e (second e)))
(define-syntax-rule (define-op/combine id)
  (define-expr-op id get-first #:same-arity? #t))

(define-op/combine +)
(define-op/combine -)
(define-op/combine &)

(define-syntax-rule (define-op/cross id)
  (define-expr-op id @+))
(define-op/cross ->)

(define-expr-op ~ get-first #:min-length 1 #:max-length 1 #:arity 2)

(: join-arity : (C→* [] [] #:rest (CListof CNat) CInt))
;; join-arity does not always produce an arity, sometimes
;; it can produce a negative integer
(define join-arity
  (λ e (@- (apply @+ e) (@* 2 (@- (length e) 1)))))
(define-syntax-rule (define-op/join id)
  (define-expr-op id join-arity #:join? #t))
(define-op/join join)

(define-expr-op <: get-second #:max-length 2 #:domain? #t)
(define-expr-op :> get-first  #:max-length 2 #:range? #t)

(define-syntax-rule (define-op/closure id)
  (define-expr-op id (const 2) #:min-length 1 #:max-length 1 #:arity 2))
(define-op/closure ^)
(define-op/closure *)

(define (const [v : CNat]) → (C→* [] [] #:rest (CListof CNat) CNat)
  (λ args v))

;; -- comprehensions -----------------------------------------------------------

(struct node/expr/comprehension node/expr
  ([decls : (CListof (C× CNode/Expr CNode/Expr))] [formula : CNode/Formula])
  #:use-super-type
  #:transparent ; TODO: opaque structs?
  #:methods gen:custom-write
  [(define (write-proc self port mode)
    (fprintf port "(comprehension ~a ~a ~a)" 
                  (node/expr-arity self) 
                  (node/expr/comprehension-decls self)
                  (node/expr/comprehension-formula self)))])

(: comprehension : (C→ (CListof (C× CNode/Expr CNode/Expr)) CNode/Formula CNode/Expr))
(define (comprehension decls formula)
  (for ([decl (in-list decls)])
    (let ([e (proj decl 1)])
      (unless (node/expr? e)
        (raise-argument-error 'set "expr?" e))
      (unless (equal? (node/expr-arity e) 1)
        (raise-argument-error 'set "decl of arity 1" e))))
  (unless (node/formula? formula)
    (raise-argument-error 'set "formula?" formula))
  (node/expr/comprehension (length decls) decls formula))

(define-syntax (set stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (with-syntax ([(rel ...) (generate-temporaries #'(r1 ...))])
       (syntax/loc stx
         (let* ([x1 (declare-anonymous-relation 1)] ...
                [decls (list (ann (tup x1 r1) : (C× Node/Expr Node/Expr)) ...)])
           (comprehension decls pred))))]))

;; -- relations ----------------------------------------------------------------

(struct node/expr/relation node/expr ([name : CString])
  #:use-super-type
  #:transparent
  #:methods gen:equal+hash
  [(define (equal-proc a b equal?-recur)
     (@and (equal?-recur (node/expr-arity a) (node/expr-arity b))
           (equal?-recur (node/expr/relation-name  a) (node/expr/relation-name b))))
   (define (hash-proc a hash-recur)
     (@+ (hash-recur (node/expr/relation-name a))
         (hash-recur (node/expr-arity a))))
   (define (hash2-proc a hash2-recur)
     (@+ (hash2-recur (node/expr/relation-name a))
         (hash2-recur (node/expr-arity a))))]
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(relation ~a ~v)"
              (node/expr-arity self)
              (node/expr/relation-name self)))])

(: declare-relation : (C→ CNat CString CNode/Expr))
(define (declare-relation arity name)
  (let ([name name])
    (node/expr/relation arity name)))

(: next-name #:mutable : Nat)
(define next-name 0)

(: declare-anonymous-relation : (C→ CNat CNode/Expr))
(define (declare-anonymous-relation arity)
  (let ([name (begin0 (format "r~v" next-name)
                      (set! next-name (add1 next-name)))])
    (node/expr/relation arity name)))

(: relation-arity : (C→ CNode/Expr CNat))
(define (relation-arity rel)
  (node/expr-arity rel))

(: relation-name : (C→ CNode/Expr CString))
(define (relation-name rel)
  (node/expr/relation-name rel))

;; -- constants ----------------------------------------------------------------

(struct node/expr/constant node/expr ([type : CSymbol])
  #:use-super-type
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "~v" (node/expr/constant-type self)))])
(define none (node/expr/constant 1 'none))
(define univ (node/expr/constant 1 'univ))
(define iden (node/expr/constant 2 'iden))

;; -- operators ----------------------------------------------------------------

(struct node/formula/op node/formula
  ([children : (CListof Any)])
  #:use-super-type
  #:transparent)

(define-syntax (define-formula-op stx)
  (syntax-case stx ()
    [(_ id Type type? checks ...)
     (with-syntax ([name (format-id #'id "node/formula/op/~a" #'id)])
       (syntax/loc stx
         (splicing-begin
           (struct name node/formula/op () #:use-super-type #:transparent
             #:reflection-name 'id)
           (define id : (C→* [] [] #:rest (CListof Type) CNode/Formula)
             (λ e
               (begin
                 (check-args 'id e type? checks ...)
                 (name e)))))))]))

(define-formula-op in CNode/Expr node/expr? #:same-arity? #t #:max-length 2)
(define-formula-op = CNode/Expr node/expr? #:same-arity? #t #:max-length 2)

(define-formula-op && CNode/Formula node/formula? #:min-length 1)
(define-formula-op || CNode/Formula node/formula? #:min-length 1)
(define-formula-op => CNode/Formula node/formula? #:min-length 2 #:max-length 2)
(define-formula-op ! CNode/Formula node/formula? #:min-length 1 #:max-length 1)       

;; -- quantifiers --------------------------------------------------------------

(struct node/formula/quantified node/formula
  ([quantifier : CSymbol]
   [decls : (CListof (C× CNode/Expr CNode/Expr))]
   [formula : CNode/Formula])
  #:use-super-type
  #:transparent ;; TODO: opaque structs?
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(~a [~a] ~a)"
              (node/formula/quantified-quantifier self)
              (node/formula/quantified-decls self)
              (node/formula/quantified-formula self)))])

(: quantified-formula :
   (C→ CSymbol (CListof (C× CNode/Expr CNode/Expr)) CNode/Formula
       CNode/Formula))
(define (quantified-formula quantifier decls formula)
  (for ([decl (in-list decls)])
    (let ([e (proj decl 1)])
      (unless (node/expr? e)
        (raise-argument-error quantifier "expr?" e))
      (unless (equal? (node/expr-arity e) 1)
        (raise-argument-error quantifier "decl of arity 1" e))))
  (unless (node/formula? formula)
    (raise-argument-error quantifier "formula?" formula))
  (node/formula/quantified quantifier decls formula))

;; -- multiplicities -----------------------------------------------------------

(struct node/formula/multiplicity node/formula
  ([mult : CSymbol] [expr : CNode/Expr])
  #:use-super-type
  #:transparent ;; TODO: opaque structs?
  #:methods gen:custom-write
  [(define (write-proc self port mode)
     (fprintf port "(~a ~a)"
              (node/formula/multiplicity-mult self)
              (node/formula/multiplicity-expr self)))])

(: multiplicity-formula : (C→ CSymbol CNode/Expr CNode/Formula))
(define (multiplicity-formula mult expr)
  (unless (node/expr? expr)
    (raise-argument-error mult "expr?" expr))
  (node/formula/multiplicity mult expr))

(define-syntax (all stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (with-syntax ([(rel ...) (generate-temporaries #'(r1 ...))])
       (syntax/loc stx
         (let* ([x1 (declare-anonymous-relation 1)] ...
                [decls (list (ann (tup x1 r1) : (C× CNode/Expr CNode/Expr)) ...)])
           (quantified-formula 'all decls pred))))]))

(define-syntax (some stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (with-syntax ([(rel ...) (generate-temporaries #'(r1 ...))])
       (syntax/loc stx
         (let* ([x1 (declare-anonymous-relation 1)] ...
                [decls (list (ann (tup x1 r1) : (C× CNode/Expr CNode/Expr)) ...)])
           (quantified-formula 'some decls pred))))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'some expr))]))

(define-syntax (no stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (with-syntax ([(rel ...) (generate-temporaries #'(r1 ...))])
       (syntax/loc stx
         (let* ([x1 (declare-anonymous-relation 1)] ...
                [decls (list (ann (tup x1 r1) : (C× CNode/Expr CNode/Expr)) ...)])
           (! (quantified-formula 'some decls pred)))))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'no expr))]))

(define-syntax (one stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (syntax/loc stx
       (multiplicity-formula 'one (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'one expr))]))

(define-syntax (lone stx)
  (syntax-case stx ()
    [(_ ([x1 r1] ...) pred)
     (syntax/loc stx
       (multiplicity-formula 'lone (set ([x1 r1] ...) pred)))]
    [(_ expr)
     (syntax/loc stx
       (multiplicity-formula 'lone expr))]))


;; PREDICATES ------------------------------------------------------------------

; Operators that take only a single argument
(: unary-op? : (C→ Any Bool))
(define (unary-op? op)
  (@or (node/expr/op/~? op)
       (node/expr/op/^? op)
       (node/expr/op/*? op)
       (node/formula/op/!? op)
       (@member? op (list ~ ^ * ! not))))
(: binary-op? : (C→ Any Bool))
(define (binary-op? op)
  (@member? op (list <: :> in = =>)))
(: nary-op? : (C→ Any Bool))
(define (nary-op? op)
  (@member? op (list + - & -> join && ||)))


;; PREFABS ---------------------------------------------------------------------

; Prefabs are functions that produce AST nodes. They're used in sketches, where
; we might want to specify an entire expression as a terminal or non-terminal
; rather than a single operator.
; A prefab needs to specify two things:
; (a) a function that takes a desired output arity k, and produces a list of
;     inputs that could produce such an output arity when the prefad is applied
; (b) a function that takes a number of inputs defined by the above function, 
;     and produces an AST.

(struct prefab
  ([inputs : (C→ Nat (Listof (Listof Nat)))]
   [ctor : (C→* [] [] #:rest (Listof Node/Expr) Node/Expr)])
  #:transparent
  #:property prop:procedure (struct-field-index ctor))
