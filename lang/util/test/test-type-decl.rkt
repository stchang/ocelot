#lang typed/rosette

(: f : (C→ Int Int))
(define f
  (λ (x) (g x x)))

(: g : (C→ Int Int Int))
(define g
  (λ (x y) (+ x y)))

