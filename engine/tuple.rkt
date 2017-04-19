#lang turnstile

(require typed/rosette/types
         (postfix-in - "tuple-untyped.rkt"))

(define-type-constructor CSetof #:arity = 1)

(provide (typed-out
          [tupleset : (C→ CNat (CSetof CNat) (CSetof CNat))]
          [tupleset-arity (C→ (CSetof CNat) CNat)]
          [tupleset-min (C→ (CSetof CNat) CNat)]
          ))
