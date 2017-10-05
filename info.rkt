#lang info

(define collection "ocelot")

(define deps '("base"
               "rackunit-lib"
               "rosette"
               "turnstile"
               "typed-rosette"))

(define build-deps '("scribble-lib" "racket-doc"))

(define scribblings '(("scribblings/ocelot.scrbl" () (experimental))))
(define pkg-desc "A solver for relational logic")
(define version "0.0.1")
(define pkg-authors '(james))

(define test-omit-paths
  '("test/symbolic-test.rkt"))
