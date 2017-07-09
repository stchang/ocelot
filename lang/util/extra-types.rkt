#lang turnstile

(provide C×
         (for-syntax ~C×))

(require (only-in turnstile/examples/stlc+tup
                  [× C×]
                  [~× ~C×]))
