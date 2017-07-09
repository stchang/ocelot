#lang turnstile

(require typed/rosette/types
         (postfix-in - racket)
         (only-in turnstile/examples/stlc+union+case if))

(provide
 (typed-out
  [+ : (Ccase-> (C→* [] [] #:rest (CListof CNat) CNat)
                (C→* [] [] #:rest (CListof CInt) CInt))]
  [- : (Ccase-> (C→* [] [] #:rest (CListof CInt) CInt))]
  [* : (Ccase-> (C→* [] [] #:rest (CListof CNat) CNat)
                (C→* [] [] #:rest (CListof CInt) CInt))]
  [expt : (C→ CNat CNat CNat)]
  [quotient : (C→ CNat CNat CNat)]
  [remainder : (C→ CNat CNat CNat)]
  [make-vector : (C→ CNat Bool (CMVectorof Bool))]
  [vector-ref : (C→ (CMVectorof Bool) CNat Bool)]
  [vector-set! : (C→ (CMVectorof Bool) CNat Bool CUnit)]
  [vector->list : (C→ (CMVectorof Bool) (CListof Bool))]
  [false? : (C→ Any CBool)]
  [equal? : (C→ Any Any CBool)]))

(provide if)
