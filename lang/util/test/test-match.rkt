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
 : (C→ CInt Any))

(check-type (match 1
              [x (ann (+ x 2) : CInt)])
            : Any
            -> 3)

(: f1 : (C→ Int Any))
(define (f1 x)
  (match x
    [0 "zero"]
    [1 "one"]
    [2 "two"]
    [3 "three"]
    [4 "four"]
    [_ "n"]))
(check-type (f1 0) : Any -> "zero")
(check-type (f1 1) : Any -> "one")
(check-type (f1 2) : Any -> "two")
(check-type (f1 3) : Any -> "three")
(check-type (f1 4) : Any -> "four")
(check-type (f1 5) : Any -> "n")
(check-type (f1 22) : Any -> "n")
(check-type (f1 (if b1 2 3)) : Any -> (if b1 "two" "three"))

(: f2 : (C→ CSymbol Any))
(define (f2 x)
  (match x
    ['a 'b]
    ['b 'c]
    ['c 'a]))
(check-type (f2 'a) : Any -> 'b)
(check-type (f2 'b) : Any -> 'c)
(check-type (f2 'c) : Any -> 'a)

(: f3 : (C→ (CList CSymbol CInt) Any))
(define (f3 x)
  (match x
    [(list 'a x) (ann x : CInt)]
    [(list 'b x) (ann x : CInt)]
    [(list 'c y) (ann y : CInt)]))
(check-type (f3 (list 'a 1)) : Any -> 1)
(check-type (f3 (list 'b 2)) : Any -> 2)
(check-type (f3 (list 'c 3)) : Any -> 3)

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
            : Any
            -> 1)

(struct bar foo ([x : CNum] [y : CNum] [z : CInt]) #:use-super-type)

(: f4 : (C→ Foo Any))
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
            : Any
            -> (list 1 2.5 3.5 6))

(check-type (f4 (foo 8))
            : Any
            -> (list 8))

(define iteb181 (if b1 8 1))

(check-type (f4 (if b1 (foo 8) (bar 1 2.5 3.5 6)))
            : Any
            -> (if b1
                   (list iteb181)
                   (list iteb181 2.5 3.5 6)))

