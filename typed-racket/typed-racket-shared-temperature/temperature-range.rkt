#lang typed/racket/base #:with-refinements

(provide constrain
         Temperature temperature?
         Range range?
         range range-a range-b
         match-define-range
         singleton
         range-avg
         range-distance-from)

(: avg : Integer Integer -> Integer)
(define (avg a b)
  (quotient (+ a b) 2))

(: constrain : (-> ([a : Integer] [b : Integer] [x : Integer])
                   #:pre (a b) (<= a b)
                   Integer))
;; ASSUME a <= b
;; PRODUCE r such that a <= r <= b
(define (constrain a b x)
  (max a (min b x)))

(define-type Temperature Integer)
(: temperature? : Any -> Boolean : Temperature)
(define (temperature? v) (exact-integer? v))

;; A Range is a (range Temperature Temperature)
;; where a <= b
(define-type Range (Refine [r : (Pairof Temperature Temperature)]
                           (<= (car r) (cdr r))))

(: range? : Any -> Boolean : Range)
(define (range? v)
  (and (pair? v)
       (temperature? (car v))
       (temperature? (cdr v))
       (<= (car v) (cdr v))))

(: range : (-> ([a : Temperature] [b : Temperature])
               #:pre (a b) (<= a b)
               Range))
(define (range a b)
  (assert (cons a b) range?))

(: range-a : (-> ([r : Range]) Temperature #:object (car r)))
(define (range-a r) (car r))

(: range-b : (-> ([r : Range]) Temperature #:object (cdr r)))
(define (range-b r) (cdr r))

(define-syntax-rule (match-define-range [a b] R)
  (begin
    (define a (range-a R))
    (define b (range-b R))))

(: singleton : Temperature -> Range)
(define (singleton T) (range T T))

(: range-avg : Range -> Temperature)
(define (range-avg R)
  (match-define-range [a b] R)
  (avg a b))

(: range-distance-from : Temperature Range -> Natural)
(define (range-distance-from T R)
  (match-define-range [a b] R)
  (cond [(< T a)  (- a T)]
        [(< b T)  (- T b)]
        [else     0]))
