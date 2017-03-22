#lang s-exp turnstile/examples/rosette/rosette2

(require "../extra-types.rkt"
         "../define-lambda-app.rkt"
         "../extra-forms.rkt"
         "../struct.rkt"
         "../generic-interfaces.rkt"
         )

(: f : (C→ Int Int))
(define f
  (λ (x) (g x x)))

(: g : (C→ Int Int Int))
(define g
  (λ (x y) (+ x y)))

