#lang turnstile

(provide tup)

(require (postfix-in - rosette)
         typed/rosette/types
         typed/rosette/match-core
         (only-in "extra-types.rkt"
           ~C×)
         (only-in "extra-forms.rkt"
           [tup tup*]))

;; ------------------------------------------------------------------------

;; Helpers

(define (maybe-vector-append- . vs)
  (if- (andmap- vector?- vs)
       (apply- vector-append- vs)
       #false))

;; ------------------------------------------------------------------------

;; Tuple Patterns

(define-syntax tup
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(tup* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (define n (stx-length #'[p ...]))
      (λ/pat-info v τ o
        (syntax-parse #'τ
          [(~C× τ_elem ...)
           #:when (stx-length=? #'[τ_elem ...] #'[p ...])
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (attribute p.get-pat-info)]
                      [τ_elem (in-list (stx->list #'[τ_elem ...]))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref v #,i) τ_elem #f))
           #:with c? (stx-andmap syntax-e #'[sub.test-concrete? ...])
           #'[([sub.x sub.τ] ... ...)
              Prop/Top
              (maybe-vector-append- sub.maybe-vec ...)
              c?]]))])))

;; ------------------------------------------------------------------------

