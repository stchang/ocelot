#lang typed/rosette

(require "../extra-types.rkt"
         "../define-lambda-app.rkt"
         "../extra-forms.rkt"
         "../struct.rkt"
         "../generic-interfaces.rkt"
         )

(struct foo ([a : Int])
  #:type-name Foo
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc this out mode)
     (fprintf out "~v" (foo-a this)))])
