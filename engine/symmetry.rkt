#lang turnstile

(require typed/rosette/types
         "interpretation.rkt"
         "../lang/bounds.rkt"
         (prefix-in ro: "symmetry-untyped.rkt"))

(provide (typed-out
          [generate-sbp : (C→ Interpretation Bounds Bool)]))

