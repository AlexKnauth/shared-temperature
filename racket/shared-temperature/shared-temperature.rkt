#lang racket/base

(provide shared-temperature
         shared-temperature*)

(require "temperature-range.rkt"
         "shared-range.rkt")

;; shared-temperature : Temperature Range Range -> Temperature
(define (shared-temperature T X Y)
  (range-avg (shared-range T X Y)))

;; shared-temperature* : Temperature [Listof Range] -> Temperature
(define (shared-temperature* T Rs)
  (range-avg (shared-range* T Rs)))
