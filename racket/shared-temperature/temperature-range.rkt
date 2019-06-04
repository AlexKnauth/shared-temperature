#lang racket/base

(provide constrain
         temperature?
         (struct-out range)
         singleton
         range-avg
         range-distance-from)

(require racket/match)

;; avg : Rational Rational -> Rational
(define (avg a b)
  (/ (+ a b) 2))

;; constrain : Rational Rational Rational -> Rational
;; ASSUME a <= b
;; PRODUCE r such that a <= r <= b
(define (constrain a b x)
  (unless (<= a b)
    (error 'constrain "expected ~a <= ~a" a b))
  (max a (min b x)))

;; A Temperature is a Rational
(define (temperature? v)
  (rational? v))

;; A Range is a (range Temperature Temperature)
;; where a <= b
(struct range [a b] #:transparent
  #:guard (λ (a b n)
            (unless (<= a b)
              (error 'range "expected ~a <= ~a" a b))
            (values a b)))

;; singleton : Temperature -> Range
(define (singleton T)
  (range T T))

;; range-avg : Range -> Temperature
(define (range-avg R)
  (match-define (range a b) R)
  (avg a b))

;; range-distance-from : Temperature Range -> NonNegRational
(define (range-distance-from T R)
  (match-define (range a b) R)
  (cond [(< T a)  (- a T)]
        [(< b T)  (- T b)]
        [else     0]))
