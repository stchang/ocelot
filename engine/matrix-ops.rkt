;#lang racket
#lang typed/rosette

(require "../lang/util/extra-forms.rkt"
         (only-in typed/rosette/base-forms unsafe-assign-type)
         "../lang/universe.rkt" "matrix.rkt"
         (prefix-in $ "../lang/util/unlifted-ops.rkt")
         ;(only-in rosette and or not for/all for*/all)
         ;(only-in rosette/base/core/bool && || => <=> !)
         )

(provide (all-defined-out))

;; ---------------------------------------------------------
#|
(: && : (C→* [] [] #:rest (CListof Bool) Bool))
(define &&
  (λ args (for/and ([arg (in-list args)]) arg)))

(: || : (C→* [] [] #:rest (CListof Bool) Bool))
(define ||
  (λ args (for/or ([arg (in-list args)]) arg)))
|#
;; ---------------------------------------------------------

(: matrix/nary-op : (C→ CUniverse
                        (→ CUniverse Matrix Matrix Matrix)
                        (CListof Matrix)
                        Matrix))
(define (matrix/nary-op universe op args)
  (for/fold ([A : Matrix (first args)])
            ([B (in-list (rest args))])
    (op universe A B)))

(: matrix/and : (C→ CUniverse Matrix Matrix Matrix))
(define (matrix/and universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (matrix (for/list ([a (in-list A)] [b (in-list B)])
              (and a b)))))

(: matrix/or : (Ccase-> (C→ CUniverse CMatrix CMatrix CMatrix)
                        (C→ CUniverse Matrix Matrix Matrix)))
(define (matrix/or universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (matrix (for/list ([a (in-list A)] [b (in-list B)])
              (or a b)))))

(: matrix/difference : (C→ CUniverse Matrix Matrix Matrix))
(define (matrix/difference universe A B)
  (for*/all ([A (matrix-entries A)][B (matrix-entries B)])
    (matrix (for/list ([a (in-list A)] [b (in-list B)])
              (and a (not b))))))

(: matrix/dot : (Ccase-> (C→ CUniverse CMatrix CMatrix CMatrix)
                         (C→ CUniverse Matrix Matrix Matrix)))
(define (matrix/dot universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (let* ([univSize (universe-size universe)]
           [arityA (matrix-entries-arity universe A)]
           [arityB (matrix-entries-arity universe B)]
           [arity (assert-type ($+ arityA arityB -2) : CNat)]
           [size ($expt univSize arity)]
           [sizeB ($expt univSize arityB)]
           [c ($quotient sizeB univSize)]
           [vB (list->vector B)]
           [res ($make-vector size #f)])
      (for ([iVal (in-list A)]
            [i (in-naturals)])
        (unless ($false? iVal)
          (let* ([rowHead ($* ($remainder i univSize) c)]
                 [rowTail ($+ rowHead c)]
                 [base ($quotient i univSize)])
            (for ([j (in-range rowHead rowTail)])
              (let ([b (vector-ref vB j)])
                (unless ($false? b)
                  (let ([retVal (&& iVal b)])
                    (unless ($false? retVal)
                      (let ([k ($+ ($* base c) ($remainder j c))])
                        ($vector-set! res k (|| ($vector-ref res k) retVal)))))))))))
      (matrix ($vector->list res)))))

(: matrix/cross : (C→ CUniverse Matrix Matrix Matrix))
(define (matrix/cross universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (matrix (for*/list ([a : Bool (in-list A)]
                        [b : Bool (in-list B)])
              (and a b)))))

(: matrix/transpose : (C→ CUniverse Matrix Matrix))
(define (matrix/transpose universe A)
  (for/all ([A (matrix-entries A)])
    (let* ([univSize (universe-size universe)])
      (matrix (for*/list ([i : CNat (in-range univSize)]
                          [j : CNat (in-range univSize)])
                (list-ref A (+ (* univSize j) i)))))))

(: matrix/closure : (C→ CUniverse Matrix Matrix))
(define (matrix/closure universe A)
  (let ([univSize (universe-size universe)])
    (for/all ([A (matrix-entries A)])
      (let loop ([Y : (CListof Bool) A] [i : CNat 1]) -> Matrix
        (let ([rY (matrix Y)])
          (if (>= i univSize)
              rY
              ;; TODO: (matrix/dot CUniverse CMatrix CMatrix) should have
              ;; type CMatrix
              (let ([Y.Y   (matrix/dot universe rY rY)])
                (if (for/and ([y (in-list (matrix-entries Y.Y))]) ($false? y))
                    rY
                    ;; TODO: (matrix/or CUniverse CMatrix CMatrix) should
                    ;; have type CMatrix
                    (let ([Y∪Y.Y (matrix/or universe rY Y.Y)])
                      (loop (matrix-entries Y∪Y.Y) (* 2 i)))))))))))

; evaluate D <: A
(: matrix/domain : (C→ CUniverse Matrix Matrix Matrix))
(define (matrix/domain universe D A)
  (let ([univSize (universe-size universe)])
    (for*/all ([A (matrix-entries A)][Ds (matrix-entries D)])
      (let* ([arityA (matrix-entries-arity universe A)]
             [denomA ($expt univSize (assert-type ($- arityA 1) : CNat))]
             [size ($expt univSize arityA)])
        (matrix (for/list ([i (in-range size)] [a (in-list A)])
                  (and a (list-ref Ds ($quotient i denomA)))))))))

; evaluate A :> R
(: matrix/range : (C→ CUniverse Matrix Matrix Matrix))
(define (matrix/range universe A R)
  (let ([univSize (universe-size universe)])
    (for*/all ([A (matrix-entries A)] [Rs (matrix-entries R)])
      (let* ([arityA (matrix-entries-arity universe A)]
             [size ($expt univSize arityA)])
        (matrix (for/list ([i (in-range size)] [a (in-list A)])
                  (and a (list-ref Rs ($remainder i univSize)))))))))

; is A a subset of B? i.e., if x in A, then x in B ≡ x in A ⇒ x in B
(: matrix/subset? : (C→ CUniverse Matrix Matrix Bool))
(define (matrix/subset? universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (apply && (for/list ([a (in-list A)] [b (in-list B)])
                (=> a b)))))

; is A equal to B? i.e. x in A iff x in B
(: matrix/equal? : (C→ CUniverse Matrix Matrix Bool))
(define (matrix/equal? universe A B)
  (for*/all ([A (matrix-entries A)] [B (matrix-entries B)])
    (apply && (for/list ([a (in-list A)] [b (in-list B)])
                (<=> a b)))))

; does A contain exactly one element?
(: matrix/one? : (C→ CUniverse Matrix Bool))
(define (matrix/one? universe A)
  (for/all ([A (matrix-entries A)])
    (let loop ([disj : Bool #f] [pred : Bool #t] [A : (CListof Bool) A]) -> Bool
      (cond
        [(null? A) (and pred disj)]
        [else (let* ([a (car A)]
                     [me (=> a (not disj))])
                (loop (or disj a) (and pred me) (cdr A)))]))))

; does A contain any element?
(: matrix/some? : (C→ CUniverse Matrix Bool))
(define (matrix/some? universe A)
  (for/all ([A (matrix-entries A)])
    (apply || A)))

; does A contain a given tuple?
(: matrix/contains? : (C→ CUniverse (CListof CSymbol) Matrix Bool))
(define (matrix/contains? universe tuple A)
  (for/all ([A (matrix-entries A)])
    (let ([arity (matrix-entries-arity universe A)])
      (unless (= arity (length tuple))
        (raise-argument-error 'matrix/contains? "tuple of correct length" tuple))
      (let ([idx (tuple->idx universe tuple)])
        (list-ref A idx)))))

