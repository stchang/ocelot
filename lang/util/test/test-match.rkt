#lang typed/rosette

(require turnstile/rackunit-typechecking
         "../match.rkt"
         "../struct.rkt"
         "struct-def.rkt")

(define-symbolic b1 b2 boolean?)

(check-type
 (λ ([x : CInt])
   (match x
     [y (ann y : CInt)]))
 : (C→ CInt CInt))

(check-type (match 1
              [x (ann (+ x 2) : CInt)])
            : CInt
            -> 3)

(: f1 : (C→ Int String))
(define (f1 x)
  (match x
    [0 "zero"]
    [1 "one"]
    [2 "two"]
    [3 "three"]
    [4 "four"]
    [_ "n"]))
(check-type (f1 0) : String -> "zero")
(check-type (f1 1) : String -> "one")
(check-type (f1 2) : String -> "two")
(check-type (f1 3) : String -> "three")
(check-type (f1 4) : String -> "four")
(check-type (f1 5) : String -> "n")
(check-type (f1 22) : String -> "n")
(check-type (f1 (if b1 2 3)) : String -> (if b1 "two" "three"))

(: f2 : (C→ CSymbol (U CSymbol)))
(define (f2 x)
  (match x
    ['a 'b]
    ['b 'c]
    ['c 'a]))
(check-type (f2 'a) : (U CSymbol) -> 'b)
(check-type (f2 'b) : (U CSymbol) -> 'c)
(check-type (f2 'c) : (U CSymbol) -> 'a)

(: f3 : (C→ (CList CSymbol CInt) (Term CInt)))
(define (f3 x)
  (match x
    [(list 'a x) (ann x : CInt)]
    [(list 'b x) (ann x : CInt)]
    [(list 'c y) (ann y : CInt)]))
(check-type (f3 (list 'a 1)) : (Term CInt) -> 1)
(check-type (f3 (list 'b 2)) : (Term CInt) -> 2)
(check-type (f3 (list 'c 3)) : (Term CInt) -> 3)

(check-type (match (list 1 '())
              [(list a (list b '()))
               (+ a 1)]
              [_
               "didn't match"])
            : Any
            -> "didn't match")

;; -------------------------------------

;; Matching with Structs

(check-type (match (foo 1)
              [(foo x) (ann x : (Term CInt))])
            : (Term CInt)
            -> 1)

(struct bar foo ([x : CNum] [y : CNum] [z : CInt]) #:use-super-type)

(: f4 : (C→ Foo (U (CList (Term CInt) Num Num (Term CInt))
                   (CList (Term CInt)))))
(define (f4 s)
  (match s
    [(bar a x y z)
     (list
      (ann a : (Term CInt))
      (ann x : Num)
      (ann y : Num)
      (ann z : (Term CInt)))]
    [(foo a)
     (list
      (ann a : (Term CInt)))]))

(check-type (f4 (bar 1 2.5 3.5 6))
            : (U (CList (Term CInt) Num Num (Term CInt))
                 (CList (Term CInt)))
            -> (list 1 2.5 3.5 6))

(check-type (f4 (foo 8))
            : (U (CList (Term CInt) Num Num (Term CInt))
                 (CList (Term CInt)))
            -> (list 8))

(define iteb181 (if b1 8 1))

(check-type (f4 (if b1 (foo 8) (bar 1 2.5 3.5 6)))
            : (U (CList (Term CInt) Num Num (Term CInt))
                 (CList (Term CInt)))
            -> (if b1
                   (list iteb181)
                   (list iteb181 2.5 3.5 6)))

