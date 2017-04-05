#lang typed/rosette

(require rackunit
         (only-in racket/base module+)
         (only-in typed/rosette/base-forms unsafe-assign-type)
         (prefix-in @ typed/rosette)
         "../lang/ast.rkt" "../lib/simplify-solve.rkt")

(define ast-cost*
  (unsafe-assign-type ast-cost : (C→ Node/Expr Int)))

(define simplify/solve*
  (unsafe-assign-type simplify/solve
                      : (C→ Node/Expr Node/Formula Node/Expr)))


; Some memory model relations that have rich type information:
; * Reads + Writes = MemoryEvent
; * Atomics ⊂ Writes
; * no Reads & Writes
; * po ⊂ (-> MemoryEvent MemoryEvent)
(: Atomics : Node/Expr)
(: Reads : Node/Expr)
(: Writes : Node/Expr)
(: MemoryEvent : Node/Expr)
(: po : Node/Expr)
(define Atomics (declare-relation 1 "Atomics"))
(define Reads (declare-relation 1 "Reads"))
(define Writes (declare-relation 1 "Writes"))
(define MemoryEvent (declare-relation 1 "MemoryEvent"))
(define po (declare-relation 2 "po"))


(: same-cost : (C→ Node/Expr Node/Expr Bool))
(define (same-cost e1 e2)
  (@= (ast-cost* e1) (ast-cost* e2)))


(module+ test
  (define ex1 (- Atomics Writes))
  (check same-cost
         (simplify/solve* ex1 (in Atomics Atomics))
         (- Atomics Writes))
  (check same-cost
         (simplify/solve* ex1 (in Atomics Writes))
         none)


  (define ex2 (+ (- Atomics Writes) (& Reads Writes)))
  (check same-cost
         (simplify/solve* ex2 (in Atomics Writes))
         (& Reads Writes))
  (check-equal?
   (simplify/solve* ex2 (&& (in Atomics Writes) (no (& Reads Writes))))
   none)


  (define ex3 (- (- MemoryEvent Reads) (- Writes Reads)))
  (check same-cost
         (simplify/solve* ex3 (&& (in (+ Reads Writes) MemoryEvent)
                                  (no (& Writes Reads))))
         (- Writes (- MemoryEvent Reads)))


  (define ex4  ; ppo for an x86 memory model
    (& po (+ (- (- po (-> Reads Atomics))
                (-> (- Writes Atomics) Reads))
             (-> (- Reads Atomics) (& Atomics (- Writes Reads))))))
  (check same-cost
         (time (simplify/solve* ex4 (&& (no (& Reads Writes))
                                        (in Atomics Writes))))
         (- po (-> (- Writes Atomics) Reads)))
  
  )