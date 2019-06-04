#lang rosette/safe

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

;; st-fair-commutative
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
          (assert (equal? (shared-temperature T X Y)
                          (shared-temperature T Y X)))))

;; st-as-good-as-any-alternative-in-total
(let ()
  (define-symbolic T temperature?)
  (define-symbolic X-a X-b Y-a Y-b temperature?)
  (define-symbolic alt temperature?)
  (define X (range X-a X-b))
  (define Y (range Y-a Y-b))
  (verify #:assume
          (begin
            (assert (is-range? X))
            (assert (is-range? Y)))
          #:guarantee
          (let ([shared (shared-temperature T X Y)])
            (assert
             (<=
              (+ (range-distance-from shared X) (range-distance-from shared Y))
              (+ (range-distance-from alt X) (range-distance-from alt Y)))))))

;; st-no-advantage-to-lying
(let ()
  (define-symbolic T temperature?)
  (define-symbolic X-a X-b X-lie-a X-lie-b Y-a Y-b temperature?)
  (define X (range X-a X-b))
  (define X-lie (range X-lie-a X-lie-b))
  (define Y (range Y-a Y-b))
  (verify #:assume
          (begin
            (assert (is-range? X))
            (assert (is-range? X-lie))
            (assert (is-range? Y)))
          #:guarantee
          (assert
           (<=
            (range-distance-from (shared-temperature T X Y) X)
            (range-distance-from (shared-temperature T X-lie Y) X)))))
