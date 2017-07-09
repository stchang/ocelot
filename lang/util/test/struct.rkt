#lang turnstile

(require typed/rosette/types
         typed/rosette/base-forms
         typed/rosette/forms-pre-match
         typed/rosette/struct)
(module+ test
  (require turnstile/rackunit-typechecking))

;; ----------------------------------------------------------------------------

(module+ test
  (struct a () #:transparent)
  (struct b () #:transparent)
  (struct c () #:transparent)
  (struct d () #:transparent)
  (struct e () #:transparent)
  (struct abc ([a : A] [b : B] [c : C]) #:transparent)

  (check-type (a) : A -> (a))
  (check-type (b) : B -> (b))
  (check-type (c) : C -> (c))
  (check-type (d) : D -> (d))
  (check-type (e) : E -> (e))
  (check-type (abc (a) (b) (c)) : CAbc -> (abc (a) (b) (c)))
  (typecheck-fail (abc (a) '3 (c))
    #:with-msg
    #;"expected B, given PosInt\n *expression: '3"
    "expected: *A, B, C\n *given: *CA, PosInt, CC\n *expressions: \\(a\\), \\(quote 3\\), \\(c\\)")

  ;; predicates
  (check-type (a? (a)) : Bool -> '#true)
  (check-type (a? (b)) : Bool -> '#false)
  (check-type (a? (abc (a) (b) (c))) : Bool -> '#false)
  (check-type (abc? (abc (a) (b) (c))) : Bool -> '#true)

  ;; inheritance
  ;; This defines a new type, CAbcde, which is a subtype of CAbc.
  (struct abcde abc ([d : D] [e : E]) #:transparent)

  (check-type (abcde (a) (b) (c) (d) (e)) : CAbcde
              -> (abcde (a) (b) (c) (d) (e)))
  (check-type (abcde (a) (b) (c) (d) (e)) : CAbc
              -> (abcde (a) (b) (c) (d) (e)))
  (typecheck-fail (abcde (a) (b) (c) '3 (e))
    #:with-msg
    #;"expected D, given PosInt\n *expression: 3"
    "expected: *A, B, C, D, E\n *given: *CA, CB, CC, PosInt, CE\n *expressions: \\(a\\), \\(b\\), \\(c\\), \\(quote 3\\), \\(e\\)")

  ;; inheritance and predicates
  (check-type (abc? (abc (a) (b) (c))) : Bool -> '#true)
  (check-type (abcde? (abcde (a) (b) (c) (d) (e))) : Bool -> '#true)
  (check-type (abc? (abcde (a) (b) (c) (d) (e))) : Bool -> '#true)
  (check-type (a? (abcde (a) (b) (c) (d) (e))) : Bool -> '#false)
  (check-type (abcde? (abc (a) (b) (c))) : Bool -> '#false)
  )
