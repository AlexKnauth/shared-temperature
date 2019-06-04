#lang rosette/safe

(provide shared-range
         shared-range*)

(require "temperature-range.rkt")

;; shared-range : Temperature Range Range -> Range
(define (shared-range T X Y)
  (match-define-range [X-a X-b] X)
  (match-define-range [Y-a Y-b] Y)
  (define a (max X-a Y-a))
  (define b (min X-b Y-b))
  (cond 
    ; If the comfortable-ranges overlap:
    [(<= a b)
     ; take that overlapping region.
     (range a b)]
    ; Otherwise one range is lower, and one range is higher,
    ; with a gap in the middle:
    [else
     ; take the temperature within the gap closest to the
     ; default temperature.
     (singleton (constrain b a T))]))

;; shared-range* : Temperature [Listof Range] -> Range
(define (shared-range* T Rs)
  (cond
    [(empty? Rs)        (singleton T)]
    [(empty? (rest Rs)) (first Rs)]
    [else
     (shared-range T (first Rs) (shared-range* T (rest Rs)))]))

;; sr-fair-commutative
;; (unsat) means it didn't find any counterexamples
(let ()
  (define-symbolic T temperature?)
  (define-symbolic X-a X-b Y-a Y-b temperature?)
  (define X (range X-a X-b))
  (define Y (range Y-a Y-b))
  (verify #:assume
          (begin
            (assert (is-range? X))
            (assert (is-range? Y)))
          #:guarantee
          (assert (equal? (shared-range T X Y)
                          (shared-range T Y X)))))

;; sr-associative
;; (unsat) means it didn't find any counterexamples
(let ()
  (define-symbolic T temperature?)
  (define-symbolic X-a X-b Y-a Y-b Z-a Z-b temperature?)
  (define X (range X-a X-b))
  (define Y (range Y-a Y-b))
  (define Z (range Z-a Z-b))
  (verify #:assume
          (begin
            (assert (is-range? X))
            (assert (is-range? Y))
            (assert (is-range? Z)))
          #:guarantee
          (assert (equal? (shared-range T (shared-range T X Y) Z)
                          (shared-range T X (shared-range T Y Z))))))
