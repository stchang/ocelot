#lang turnstile

(provide for/fold for for/list for/and for/or for/hash
         for*/list
         in-list in-naturals in-range
         and when unless cond else
         ~v format fprintf
         length list-ref first rest second map foldl member? cartesian-product*
         log exact-round
         begin0 hash-ref tup proj
         raise-argument-error raise-arguments-error void exn:fail?
         make-vector vector-ref vector-set! vector->list
         define-syntax define-syntax-rule
         (rename-out [begin- splicing-begin]))

(require "require.rkt"
         (subtract-in typed/rosette
                      "define-lambda-app.rkt"
                      "extra-types.rkt")
         (prefix-in tro: typed/rosette)
         (only-in turnstile/examples/stlc+tup
                  tup proj)
         (prefix-in ro: rosette)
         (except-in "define-lambda-app.rkt" #%app)
         "extra-types.rkt")

;; ----------------------------------------------------------------------------

;; For Loops and Sequences

(define-typed-syntax for/fold
  [(_ ([acc:id : τ_acc e_init])
      ([x:id seq:expr] ...)
      body:expr ...+) ≫
   [⊢ e_init ≫ e_init- ⇐ τ_acc]
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[acc ≫ acc- : τ_acc]
    [x ≫ x- : τ_x] ...
    ⊢ (begin body ...) ≫ body- ⇐ τ_acc]
   --------
   [⊢ (ro:for/fold ([acc- e_init-])
                   ([x- seq-] ...)
        body-)
      ⇒ τ_acc]])

(define-typed-syntax for
  [(_ ([x:id seq:expr] ...) body:expr ...+) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ (begin body ...) ≫ body- ⇐ Void]
   --------
   [⊢ (ro:for ([x- seq-] ...) body-) ⇒ Void]])

(define-typed-syntax for/list
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (ro:for/list ([x- seq-] ...) body-)
      ⇒ (CListof τ_body)]])

(define-typed-syntax for*/list
  #:datum-literals [:]
  [(_ ([x:id : τ_x:type seq:expr] ...) body:expr) ≫
   #:do [(define (triangle lst)
           (for/list ([i (in-range (stx-length lst))])
             (take (stx->list lst) i)))]
   #:with [[x_prev ...] ...] (triangle #'[x ...])
   #:with [[τ_x_prev ...] ...] (triangle #'[τ_x ...])
   [[x_prev ≫ x_prev- : τ_x_prev] ...
    ⊢ seq ≫ seq- ⇐ (CSequenceof τ_x)]
   ...
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   #:with [[x-_prev ...] ...] (triangle #'[x- ...])
   --------
   [⊢ (ro:for*/list ([x- (let- ([x_prev- x-_prev] ...) seq-)] ...)
        body-)
      ⇒ (CListof τ_body)]])

(define-typed-syntax for/and
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (ro:for/and ([x- seq-] ...) body-)
      ⇒ (U Bool τ_body)]])

(define-typed-syntax for/or
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   --------
   [⊢ (ro:for/or ([x- seq-] ...) body-)
      ⇒ (U Bool τ_body)]])

;; This behaves slightly differently from the racket
;; version: the body expression must produce a 2-tuple
;; instead of using multiple values.
(define-typed-syntax for/hash
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ (~C× τ_key τ_val)]
   --------
   [⊢ (ro:for/hash ([x- seq-] ...) (apply- values- body-))
      ⇒ (CHashof τ_key τ_val)]])

(define-typed-syntax in-list
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ : (~CListof τ)]
   --------
   [⊢ (ro:in-list e-) ⇒ : (CSequenceof τ)]])

(define-typed-syntax in-naturals
  [(_) ≫
   --------
   [⊢ (ro:in-naturals) ⇒ : (CSequenceof CNat)]])

(define-typed-syntax in-range
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇐ CNat]
   --------
   [⊢ (ro:in-range e-) ⇒ (CSequenceof CNat)]]
  [(_ a:expr b:expr) ≫
   [⊢ a ≫ a- ⇐ CNat]
   [⊢ b ≫ b- ⇐ CNat]
   --------
   [⊢ (ro:in-range a- b-) ⇒ (CSequenceof CNat)]])

;; ----------------------------------------------------------------------------

;; Conditionals

(define-typed-syntax when
  [(_ condition:expr body:expr ...+) ≫
   [⊢ condition ≫ condition- ⇐ Bool]
   [⊢ (begin body ...) ≫ body- ⇒ τ]
   --------
   [⊢ (ro:when condition- body-) ⇒ (U τ Void)]])

(define-typed-syntax unless
  [(_ condition:expr body:expr ...+) ≫
   [⊢ condition ≫ condition- ⇐ Bool]
   [⊢ (begin body ...) ≫ body- ⇒ τ]
   --------
   [⊢ (ro:unless condition- body-) ⇒ (U τ Void)]])

(define-typed-syntax and
  [(_ e:expr ...) ≫
   [⊢ [e ≫ e- (⇐ Bool) (⇒ τ_e)] ...]
   #:with [[CBool* _] ...] #`[[#,((current-type-eval) #'CBool) τ_e] ...]
   #:with τ_out (if (typechecks? #'[τ_e ...] #'[CBool* ...])
                    #'CBool
                    #'Bool)
   --------
   [⊢ (ro:and e- ...) ⇒ τ_out]])

(define-syntax-parser cond
  #:literals [else]
  [(_ [else ~! body:expr])
   #'body]
  [(_ [(~and b:expr (~not else)) ~! v:expr] rst ... [else body:expr])
   (quasisyntax/loc this-syntax
     (if b
         v
         #,(syntax/loc this-syntax (cond rst ... [else body]))))])

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
   [⊢ (ro:fprintf out- fmt v- ...) ⇒ CUnit]])

;; ----------------------------------------------------------------------------

;; Lists

(define-typed-syntax length
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof _)]
   --------
   [⊢ (ro:length lst-) ⇒ CNat]]
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~U* (~CListof _))]
   --------
   [⊢ (ro:length lst-) ⇒ Nat]])

(define-typed-syntax list-ref
  [(_ lst:expr i:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref lst- i-) ⇒ τ]]
  [(_ lst:expr i:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~or (~CListof τ)
                        (~U* (~CListof τ)))]
   [⊢ i ≫ i- ⇐ Nat]
   --------
   [⊢ (ro:list-ref lst- i-) ⇒ (U τ)]])

(define-typed-syntax first
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:first lst-) ⇒ τ]])

(define-typed-syntax rest
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:rest lst-) ⇒ (CListof τ)]])

(define-typed-syntax second
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:second lst-) ⇒ τ]])

(define-typed-syntax map
  [(_ f:expr lst:expr) ⇐ (~CListof Y) ≫
   [⊢ f ≫ f- ⇒ (~C→ X Y*)]
   ; Y* must be usable as Y, because the Y* value will be used
   ; as an element the return value
   [Y* τ⊑ Y #:for f]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:map f- lst-)]]
  [(_ f:expr lst:expr) ≫
   [⊢ f ≫ f- ⇒ (~C→ X Y)]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:map f- lst-) ⇒ (CListof Y)]])

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

(define member
  (unsafe-assign-type ro:member :
                      (C→ Any (Listof Any) Any)))

(: member? : (C→ Any (Listof Any) Bool))
(define (member? v lov)
  (if (member v lov) #true #false))

(define-typed-syntax cartesian-product*
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof (~CListof τ))]
   --------
   [⊢ (ro:apply ro:cartesian-product lst-)]])

;; ----------------------------------------------------------------------------

;; Extra Arithmetic

(define log
  (unsafe-assign-type ro:log : (C→ CNum CNum)))

(define exact-round
  (unsafe-assign-type ro:exact-round :
                      (Ccase-> (C→ CNat CNat)
                               (C→ Nat Nat)
                               (C→ CNum CInt)
                               (C→ Num Int))))

;; ----------------------------------------------------------------------------

;; Other

(define-typed-syntax begin0
  [(_ e0:expr e:expr ...) ≫
   [⊢ e0 ≫ e0- ⇒ τ]
   [⊢ [e ≫ e- ⇐ Void] ...]
   --------
   [⊢ (ro:begin0 e0- e- ...) ⇒ τ]])

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

(define exn:fail? (unsafe-assign-type ro:exn:fail? : (C→ Any Bool)))

(define-typed-syntax make-vector
  [(_ size:expr v:expr) ≫
   [⊢ size ≫ size- ⇐ CNat]
   [⊢ v ≫ v- ⇒ τ]
   --------
   [⊢ (ro:make-vector size- v-) ⇒ (CMVectorof τ)]])

(define-typed-syntax vector-ref
  [(_ v:expr i:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:vector-ref v- i-) ⇒ τ]])

(define-typed-syntax vector-set!
  [(_ v:expr i:expr x:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   [⊢ i ≫ i- ⇐ CNat]
   [⊢ x ≫ x- ⇐ τ]
   --------
   [⊢ (ro:vector-set! v- i- x-) ⇒ CUnit]])

(define-typed-syntax vector->list
  [(_ v:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   --------
   [⊢ (ro:vector->list v-) ⇒ (CListof τ)]])
