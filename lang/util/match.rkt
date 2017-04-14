#lang turnstile

(provide match
         _ var quote
         and or not
         list
         tup
         (for-syntax prop:match-pattern-id
                     predicate-accessor-pattern-id))

(require (postfix-in - rosette)
         typed/rosette/types
         (only-in typed/rosette
           [#%app app*]
           [quote quote*]
           [and and*] [or or*] [not not*]
           [list list*])
         (only-in "extra-types.rkt"
           ~C×)
         (only-in "extra-forms.rkt"
           [tup tup*])
         (for-syntax syntax/parse/class/local-value))

;; ------------------------------------------------------------------------

;; Match Patterns

;;  pat        ::= derived-pat
;;               | literal-pat
;;               | id-pat

;; derived-pat ::= match-pattern-id
;;               | (match-pattern-id . rest)

;; literal-pat ::= bool
;;               | string
;;               | number

;; id-pat      ::= id   ; not match-pattern-id or `...`

;; derived pats will include patterns like
;;               | _
;;               | (var id)
;;               | (quote datum)
;;               | (and pat ...)
;;               | (or pat ...)   ; TODO: branches conflict?
;;               | (not pat)
;;               | (list lv-pat ...)

(begin-for-syntax
  (define-values [prop:match-pattern-id
                  match-pattern-id?
                  match-pattern-id-ref]
    (make-struct-type-property 'match-pattern-id))
  (define-syntax-class match-pat-id
    #:attributes [get-get-pat-info]
    [pattern (~var id (local-value match-pattern-id?))
      #:attr get-get-pat-info
      (get-match-pattern-id-function (attribute id.local-value))])
  (define (get-match-pattern-id-function value)
    (cond [(match-pattern-id? value)
           (get-match-pattern-id-function
            ((match-pattern-id-ref value) value))]
          [else value]))

  ;; A PatInfo is a (StxListof (StxList Id TypeStx))
  (define-syntax-class pat-info
    #:attributes [[x 1] [τ 1] maybe-vec]
    [pattern [([x:id τ:expr] ...) maybe-vec]])
  (define-syntax-rule (λ/pat-info v-pat τ-pat body ...)
    (λ (v τ)
      (syntax-parse (list v τ)
        [[v-pat τ-pat] body ...])))

  ;; map-app2 : A B (Listof [A B -> C]) -> (Listof C)
  (define (map-app2 a b fs)
    (for/list ([f (in-list fs)])
      (f a b)))

  (define-syntax-class pat
    #:attributes [get-pat-info]
    ;; get-pat-info : [TypeStx -> PatInfo]
    [pattern :derived-pat]
    [pattern :literal-pat]
    [pattern :id-pat])

  (define-syntax-class id-pat
    #:attributes [get-pat-info]
    #:datum-literals [_ ...]
    [pattern (~and x:id (~not (~or :match-pat-id ...)))
      #:attr get-pat-info
      (λ/pat-info v τ #'[([x τ]) (vector-immutable- v)])])

  (define-syntax-class literal-pat
    #:attributes [get-pat-info]
    [pattern b:boolean
      #:attr get-pat-info
      (λ/pat-info v τ #'[() (if- (eq?- v (quote- b)) #() #f)])]
    [pattern s:str
      #:attr get-pat-info
      (λ/pat-info v τ #'[() (if- (eq?- v (quote- s)) #() #f)])]
    [pattern n:number
      #:attr get-pat-info
      (λ/pat-info v τ #'[() (if- (eq?- v (quote- n)) #() #f)])]
    )

  (define-syntax-class derived-pat
    #:attributes [get-pat-info]
    [pattern (~and stx id:match-pat-id)
      #:attr get-pat-info
      (derived-pat->get-info (attribute id.get-get-pat-info) #'stx)]
    [pattern (~and stx (id:match-pat-id . _))
      #:attr get-pat-info
      (derived-pat->get-info (attribute id.get-get-pat-info) #'stx)])

  (define (derived-pat->get-info get-get-pat-info stx)
    (define intro (make-syntax-introducer))
    (define stx* (intro stx))
    (define get-pat-info* (get-get-pat-info stx*))
    (define (get-pat-info v τ)
      (intro (get-pat-info* v τ)))
    get-pat-info)
  )

;; ------------------------------------------------------------------------

;; Match

(define-typed-syntax match
  [(_ val:expr [pat:pat body:expr] ...) ≫
   [⊢ val ≫ val- ⇒ τ_val]
   #:with tmp (generate-temporary #'val)
   #:with [p:pat-info ...]
   (map-app2 #'tmp #'τ_val (attribute pat.get-pat-info))
   [[p.x ≫ x- : p.τ] ...
    ⊢ body ≫ body- ⇒ τ_body]
   ...
   #:with failure-
   #'(assert- #false (format- "no matching clause for ~v" tmp))
   #:with matching-expr-
   (for/fold ([acc #'failure-])
             ([xs- (in-list (reverse (stx->list #'[[x- ...] ...])))]
              [maybe-vec (in-list (reverse (stx->list #'[p.maybe-vec ...])))]
              [body- (in-list (reverse (stx->list #'[body- ...])))])
     (with-syntax ([acc acc]
                   [v-tmp (generate-temporary)]
                   [maybe-vec maybe-vec]
                   [(x- ...) xs-]
                   [(i- ...) (range (stx-length xs-))]
                   [body- body-])
     #'(let- ([v-tmp maybe-vec])
        (if- v-tmp
             (let- ([x- (vector-ref- v-tmp i-)] ...)
               body-)
             acc))))
   --------
   [⊢ (let- ([tmp val-]) matching-expr-)
      ⇒ Any]])

;; ------------------------------------------------------------------------

;; Match-Pattern Ids

(begin-for-syntax
  (define match-pattern-id
    (local [(struct match-pattern-id [f]
              #:property prop:match-pattern-id
              (λ (this) (match-pattern-id-f this)))]
      match-pattern-id))
  (define macro/match-pattern-id
    (local [(struct macro/match-pattern-id [macro-f match-f]
              #:property prop:procedure
              (struct-field-index macro-f)
              #:property prop:match-pattern-id
              (λ (this) (macro/match-pattern-id-match-f this)))]
      macro/match-pattern-id)))

(define-syntax _
  (match-pattern-id
   (syntax-parser
     [_ (λ/pat-info v τ #'[() #()])])))

(define-syntax var
  (match-pattern-id
   (syntax-parser
     [(_ x:id)
      (λ/pat-info v τ #'[([x τ]) (vector-immutable- v)])])))

(define-syntax quote
  (macro/match-pattern-id
   (syntax-parser
     [(_ datum) #'(quote* datum)])
   (syntax-parser
     [(_ datum)
      (λ/pat-info v τ #'[() (if- (eq?- v (quote- datum)) #() #f)])])))

(define-syntax and
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(and* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (λ/pat-info v τ
        #:with [sub:pat-info ...]
        (map-app2 #'v #'τ (attribute p.get-pat-info))
        #'[([sub.x sub.τ] ... ...)
           (maybe-vector-append- sub.maybe-vec ...)])])))

(define-syntax or
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(or* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (λ/pat-info v τ
        #:with [sub:pat-info ...]
        (map-app2 #'v #'τ (attribute p.get-pat-info))
        #'[()
           (if- (or- sub.maybe-vec ...) #() #f)])])))

(define-syntax not
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr) #'(app* not* e)])
   (syntax-parser
     [(_ p:pat)
      (λ/pat-info v τ
        #:with sub:pat-info ((attribute p.get-pat-info) #'v #'τ)
        #'[() (if- (not- sub.maybe-vec) #() #f)])])))

;; ------------------------------------------------------------------------

;; Helpers

(define (maybe-vector-append- . vs)
  (if- (andmap- vector?- vs)
       (apply- vector-append- vs)
       #false))

;; ------------------------------------------------------------------------

;; List Patterns

;; list-pat    ::= (list lv-pat ...)
;;               | (list* lv-pat ... pat)

;; lv-pat      ::= eh-pat ooo
;;               | pat

;; eh-pat      ::= pat      ; TODO: EH-or patterns?

;; ooo         ::= ...

;; TODO: implement lv-pats and ellipses

(define-syntax list
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(list* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (define n (stx-length #'[p ...]))
      (λ/pat-info v τ
        (syntax-parse #'τ
          [(~CList τ_elem ...)
           #:when (stx-length=? #'[τ_elem ...] #'[p ...])
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (attribute p.get-pat-info)]
                      [τ_elem (in-list (stx->list #'[τ_elem ...]))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref v #,i) τ_elem))
           #'[([sub.x sub.τ] ... ...)
              (maybe-vector-append- sub.maybe-vec ...)]]
          [_
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (in-list (attribute p.get-pat-info))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref v #,i) #'Any))
           #`[([sub.x sub.τ] ... ...)
              (and- (list?- v)
                    (=- #,n (length- v))
                    (maybe-vector-append- sub.maybe-vec ...))]]))])))

;; ------------------------------------------------------------------------

;; Tuple Patterns

(define-syntax tup
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(tup* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (define n (stx-length #'[p ...]))
      (λ/pat-info v τ
        (syntax-parse #'τ
          [(~C× τ_elem ...)
           #:when (stx-length=? #'[τ_elem ...] #'[p ...])
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (attribute p.get-pat-info)]
                      [τ_elem (in-list (stx->list #'[τ_elem ...]))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref v #,i) τ_elem))
           #'[([sub.x sub.τ] ... ...)
              (maybe-vector-append- sub.maybe-vec ...)]]))])))

;; ------------------------------------------------------------------------

;; Predicate-Accessor Patterns

;; It's on the user to supply a predicate that implies that the accessors
;; won't fail, and will produce values of the given field types.

(begin-for-syntax
  (struct predicate-accessor-pattern-id [predicate accessors field-types]
    #:property prop:match-pattern-id
    (λ (this)
      (match-define
        (predicate-accessor-pattern-id predicate accessors field-types)
        this)
      (define n (length accessors))
      (unless (= n (length field-types))
        (error 'precidate-accessor-pattern-id
          "must have the same number of accessors and field types"))
      (syntax-parser
        [(_ sub-pat:pat ...)
         #:fail-unless (= n (stx-length #'[sub-pat ...]))
         (format "expected ~v sub-patterns" n)
         (λ/pat-info v τ
           #:do [(define τ-concrete? (concrete? #'τ))]
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (in-list (attribute sub-pat.get-pat-info))]
                      [accessor (in-list accessors)]
                      [field-type (in-list field-types)])
             (get-pat-info #`(#,accessor v)
                           (if τ-concrete?
                               field-type
                               (type-merge field-type field-type))))
           #`[([sub.x sub.τ] ... ...)
              (and- (#,predicate v)
                    (maybe-vector-append- sub.maybe-vec ...))])])))
  )

;; TODO: make this work with occurrence typing

#;
(define-syntax predicate-accessor-pattern
  (match-pattern-id
   (syntax-parser
     [(_ pred:expr [accessor:expr sub-pat:pat] ...)
      [⊢ pred ≫ pred- ⇒ (~C→ τ_v _ : #:+ τ_v+)]
      [⊢ [accessor ≫ accessor- ⇒ (~C→ τ_in τ_out)] ...]
      [τ_v+ τ⊑ τ_in] ...
      (λ/pat-info v τ
        [τ_v τ⊑ τ]
        #:with [sub:pat-info ...]
        (for/list ([get-pat-info (in-list (attribute p.get-pat-info))]
                   [accessor- (in-list (stx->list #'[accessor- ...]))]
                   [τ_out (in-list (stx->list #'[τ_out ...]))])
          (get-pat-info #`(#,accessor- v) τ_out))
        #`[([sub.x sub.τ] ... ...)
           (and- (pred- v)
                 (maybe-vector-append- sub.maybe-vec ...))])])))


