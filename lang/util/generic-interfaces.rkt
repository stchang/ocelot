#lang turnstile

(provide gen:custom-write gen:equal+hash)

(require (only-in turnstile/examples/rosette/rosette2 CU CBool CInt CNat Any)
         (only-in "extra-types.rkt" C→ COutputPort CVoid)
         "struct.rkt")
(module+ test
  (require "require.rkt"
           (subtract-in turnstile/examples/rosette/rosette2
                        "define-lambda-app.rkt"
                        "extra-types.rkt"
                        "extra-forms.rkt")
           "define-lambda-app.rkt"
           "extra-types.rkt"
           "extra-forms.rkt"
           "struct.rkt"))

(define-syntax gen:custom-write
  (generic-interface-type-info
   #'gen:custom-write-
   (λ (τ)
     (list
      (list 'write-proc
            #`(C→ #,τ COutputPort (CU CBool CNat) CVoid))))))

(define-syntax gen:equal+hash
  (generic-interface-type-info
   #'gen:equal+hash-
   (λ (τ)
     (list
      (list 'equal-proc
            #`(C→ #,τ #,τ (C→ Any Any CBool) CBool))
      (list 'hash-proc
            #`(C→ #,τ (C→ Any CInt) CInt))
      (list 'hash2-proc
            #`(C→ #,τ (C→ Any CInt) CInt))))))

;; ----------------------------------------------------------------------------

(module+ test
  (struct foo ([a : Int])
    #:type-name Foo
    #:transparent
    #:methods gen:custom-write
    [(define (write-proc this out mode)
       (fprintf out "~v" (foo-a this)))])
  )
