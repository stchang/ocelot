#lang typed/rosette

(struct foo ([a : Int])
  #:type-name Foo
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc this out mode)
     (fprintf out "~v" (foo-a this)))])
