#lang turnstile

(provide for for/list for/and for/hash
         in-list in-naturals
         when unless
         ~v format fprintf
         length first second foldl
         +
         hash-ref tup
         raise-argument-error raise-arguments-error void
         define-syntax define-syntax-rule
         (rename-out [begin- splicing-begin]))

(require (except-in turnstile/examples/rosette/rosette2
                    define λ #%app
                    C→ ~C→
                    Ccase-> ~Ccase->)
         (prefix-in tro: turnstile/examples/rosette/rosette2)
         (only-in turnstile/examples/stlc+tup
                  tup)
         (prefix-in ro: rosette)
         (except-in "define-lambda-app.rkt" #%app)
         "extra-types.rkt")

;; ----------------------------------------------------------------------------

;; For Loops and Sequences

(define-typed-syntax for
  [(_ ([x:id seq:expr] ...) body:expr ...+) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ (begin body ...) ≫ body- ⇐ Void]
   --------
   [⊢ (for- ([x- seq-] ...) body-) ⇒ Void]])

(define-typed-syntax for/list
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (for/list- ([x- seq-] ...) body-)
      ⇒ (CListof τ_body)]])

(define-typed-syntax for/and
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (for/and- ([x- seq-] ...) body-)
      ⇒ (CListof (U Bool τ_body))]])

;; This behaves slightly differently from the racket
;; version: the body expression must produce a 2-tuple
;; instead of using multiple values.
(define-typed-syntax for/hash
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ (~C× τ_key τ_val)]
   --------
   [⊢ (for/hash- ([x- seq-] ...) (apply- values- body-))
      ⇒ (CHashof τ_key τ_val)]])

(define-typed-syntax in-list
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ : (~CListof τ)]
   --------
   [⊢ (in-list- e-) ⇒ : (CSequenceof τ)]])

(define-typed-syntax in-naturals
  [(_) ≫
   --------
   [⊢ (in-naturals-) ⇒ : (CSequenceof CNat)]])

;; ----------------------------------------------------------------------------

;; Conditionals

(define-typed-syntax when
  [(_ condition:expr body:expr) ≫
   [⊢ condition ≫ condition- ⇐ Bool]
   [⊢ body ≫ body- ⇒ τ]
   --------
   [⊢ (ro:when condition- body-) ⇒ (U τ Void)]])

(define-typed-syntax unless
  [(_ condition:expr body:expr) ≫
   [⊢ condition ≫ condition- ⇐ Bool]
   [⊢ body ≫ body- ⇒ τ]
   --------
   [⊢ (ro:unless condition- body-) ⇒ (U τ Void)]])

;; ----------------------------------------------------------------------------

;; Formatting values as strings

(begin-for-syntax
  ;; format-string-matches? : String [Listof Any] -> Bool
  (define (format-string-matches? fmt vals)
    (with-handlers ([exn:fail? (λ (e) #false)])
      (apply format fmt vals)
      #true))
  )

(define ~v (unsafe-assign-type ro:~v : (C→ Any CString)))

(define-typed-syntax format
  [(_ fmt:str v:expr ...) ≫
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:format fmt v- ...) ⇒ CString]])

(define-typed-syntax fprintf
  [(_ out:expr fmt:str v:expr ...) ≫
   [⊢ out ≫ out- ⇐ COutputPort]
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:fprintf out- fmt v- ...) ⇒ CVoid]])

;; ----------------------------------------------------------------------------

;; Lists

(define-typed-syntax length
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof _)]
   --------
   [⊢ (length- lst-) ⇒ CNat]])

(define-typed-syntax first
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:first lst-) ⇒ τ]])

(define-typed-syntax second
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:second lst-) ⇒ τ]])

(define-typed-syntax foldl
  [(_ f:expr base:expr lst:expr) ⇐ Y ≫
   [⊢ f ≫ f- ⇒ (~C→ X Y* Z)]
   ; Z must be usable as Y*, because the Z value will be
   ; used as the Y* argument on the next iteration
   [Z τ⊑ Y* #:for f]
   ; Z must be usable as Y, because the Z value will be used
   ; as the return value
   [Z τ⊑ Y #:for f]
   ; Y must be usable as Y*, because the base Y value will
   ; be used as the Y* argument on the first iteration
   [Y τ⊑ Y* #:for f]
   ; base must be usable as Y, because the base value will
   ; be used as the return value
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-)]]
  [(_ f:expr base:expr lst:expr) ⇐ Y ≫
   ; TODO: fix this to take X into account when choosing
   ; which case to commit to
   [⊢ f ≫ f- ⇒
      (~Ccase-> _ ...
                (~and (~C→ X Y* Z)
                      (~fail #:unless (typecheck? #'Z #'Y*))
                      (~fail #:unless (typecheck? #'Z #'Y))
                      (~fail #:unless (typecheck? #'Y #'Y*)))
                _ ...)]
   ; base must be usable as Y, because the base value will
   ; be used as the return value
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-)]]
  [(_ f:expr base:expr lst:expr) ≫
   ; TODO: fix this to try all options in the Ccase->
   [⊢ f ≫ f- ⇒ (~Ccase-> _ ... (~C→ X Y Z))]
   ; Z must be usable as Y, because the Z value will be used
   ; as the Y argument on the next iteration
   [Z τ⊑ Y #:for f]
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-) ⇒ Y]])

;; ----------------------------------------------------------------------------

;; Extra Arithmetic

(define +
  (unsafe-assign-type ro:+ :
                      (Ccase-> (C→ CNat CNat CNat)
                               (C→ CNat CNat CNat CNat)
                               (C→ CNat CNat CNat CNat CNat)
                               (C→ Nat Nat Nat)
                               (C→ Nat Nat Nat Nat)
                               (C→ Nat Nat Nat Nat Nat)
                               (C→* [] [] #:rest (CListof Nat) Nat)
                               (C→ CInt CInt CInt)
                               (C→ CInt CInt CInt CInt)
                               (C→ CInt CInt CInt CInt CInt)
                               (C→ Int Int Int)
                               (C→ Int Int Int Int)
                               (C→ Int Int Int Int Int)
                               (C→* [] [] #:rest (CListof Int) Int)
                               (C→ CNum CNum CNum)
                               (C→ CNum CNum CNum CNum)
                               (C→ CNum CNum CNum CNum CNum)
                               (C→ Num Num Num)
                               (C→ Num Num Num Num)
                               (C→ Num Num Num Num Num)
                               (C→* [] [] #:rest (CListof Num) Num))))

;; ----------------------------------------------------------------------------

;; Other

(define-typed-syntax hash-ref
  [(_ hsh:expr key:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   --------
   [⊢ (hash-ref- hsh- key-) ⇒ : τ_val]])

(define-typed-syntax raise-arguments-error
  [(_ name message (~seq field v) ...) ≫
   [⊢ name ≫ name- ⇐ CSymbol]
   [⊢ message ≫ message- ⇐ CString]
   [⊢ [field ≫ field- ⇐ CString] ...]
   [⊢ [v ≫ v- ⇐ Any] ...]
   #:with [[field/v- ...] ...] #'[[field- v-] ...]
   --------
   [⊢ (ro:raise-arguments-error name- message- field/v- ... ...)
      ⇒ Nothing]])

(define raise-argument-error
  (unsafe-assign-type ro:raise-argument-error
                      : (C→ CSymbol CString Any Nothing)))

(define void (unsafe-assign-type ro:void : (C→ CVoid)))
