#lang rosette/safe

(provide constrain
         temperature?
         (struct-out range)
         is-range?
         match-define-range
         singleton
         range-avg
         range-distance-from)

;; avg : Rational Rational -> Rational
(define (avg a b)
  (/ (+ a b) 2))

;; constrain : Rational Rational Rational -> Rational
;; ASSUME a <= b
;; PRODUCE r such that a <= r <= b
(define (constrain a b x)
  (assert (<= a b))
  (max a (min b x)))

;; A Temperature is a Real
(define temperature? real?)

;; A Range is a (range Temperature Temperature)
;; where a <= b
(struct range [a b] #:transparent)

(define (is-range? R)
  (and (range? R)
       (<= (range-a R) (range-b R))))

;; singleton : Temperature -> Range
(define (singleton T)
  (range T T))

(define-syntax-rule (match-define-range [a b] R)
  (begin
    (define a (range-a R))
    (define b (range-b R))))

;; range-avg : Range -> Temperature
(define (range-avg R)
  (match-define-range [a b] R)
  (avg a b))

;; range-distance-from : Temperature Range -> NonNegRational
(define (range-distance-from T R)
  (match-define-range [a b] R)
  (cond [(< T a)  (- a T)]
        [(< b T)  (- T b)]
        [else     0]))
