#lang typed/rosette

(require "../lang/util/struct.rkt"
         "../lang/util/extra-forms.rkt"
         (prefix-in $ racket)
         "../lang/universe.rkt")
(provide (all-defined-out))

(struct matrix ([entries : (CListof Bool)])
  #:transparent)

(: matrix-arity : (C→ CUniverse CMatrix Nat))
(define (matrix-arity universe mat)
  (matrix-entries-arity universe (matrix-entries mat)))

(: matrix-entries-arity : (C→ CUniverse (CListof Bool) CNat))
(define (matrix-entries-arity universe mat)
  (let ([len (length mat)])
    (assert-type
     (exact-round (/ (log len) (log (universe-size universe))))
     : CNat)))

(: tuple->idx : (C→ CUniverse (CListof CSymbol) CNat))
(define (tuple->idx universe tuple)
  (let ([base (length (universe-atoms universe))])
    (let loop ([idx : CNat 0] [mult : CNat 1] [tuple : (CListof CSymbol) (reverse tuple)]) -> CNat
      (if (empty? tuple)
          idx
          (loop (+ idx (* ((universe-inverse universe) (car tuple)) mult))
                (* mult base)
                (cdr tuple))))))

(: idx->tuple : (C→ CUniverse CNat CNat (CListof CSymbol)))
(define (idx->tuple universe arity idx)
  (let ([usize (universe-size universe)])
    (for/list ([i (in-range arity)])
      (list-ref (universe-atoms universe)
                (assert-type
                 (remainder (quotient idx (expt usize (- arity i 1))) usize)
                 : CNat)))))

(: singleton-matrix : (C→ CUniverse CNat CMatrix))
(define (singleton-matrix universe idx)
  (matrix (for/list ([i (in-range (universe-size universe))]) (= i idx))))
