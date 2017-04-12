#lang typed/rosette

(require turnstile/rackunit-typechecking
         "struct-def.rkt")

(: foo-a* : (C→ CFoo CInt))
(define (foo-a* f)
  (foo-a f))

(check-type (foo 1) : CFoo)

(: x : CFoo)
(define x (foo 1))
(check-type x : CFoo)
(check-type (foo-a x) : CInt -> 1)
