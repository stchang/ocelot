#lang typed/rosette

(require "util/provide.rkt"
         "util/extra-types.rkt"
         "util/extra-forms.rkt")

(provide (except-out (all-defined-out) universe)
         (rename-out [make-universe universe]))

;; universe --------------------------------------------------------------------

(struct universe
  ([atoms : (CListof CSymbol)] [inverse : (C→ CSymbol CNat)])
  #:type-name Universe
  #:transparent)

(define (make-universe [atoms : (CListof CSymbol)]) → CUniverse
  (let ([inverse (for/hash ([a (in-list atoms)]
                            [i (in-naturals)])
                   (tup a i))])
    (universe
     atoms
     (λ ([t : CSymbol]) (hash-ref inverse t)))))

(define (universe-size [universe : CUniverse]) → CNat
  (length (universe-atoms universe)))

