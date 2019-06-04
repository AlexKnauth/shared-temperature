#lang racket/base

(provide shared-range
         shared-range*)

(require racket/match
         "temperature-range.rkt")

;; shared-range : Temperature Range Range -> Range
(define (shared-range T X Y)
  (match-define (range X-a X-b) X)
  (match-define (range Y-a Y-b) Y)
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
  (match Rs
    ['()         (singleton T)]
    [(list R)    R]
    [(cons R Rs) (shared-range T R (shared-range* T Rs))]))
