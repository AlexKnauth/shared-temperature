(define-fun avg ((a Real) (b Real)) Real
  (/ (+ a b) 2))

(define-fun max ((a Real) (b Real)) Real
  (if (< a b) b a))

(define-fun min ((a Real) (b Real)) Real
  (if (< a b) a b))

(define-fun constrain ((a Real) (b Real) (x Real)) Real
  (max a (min b x)))

(define-fun distance ((a Real) (b Real)) Real
  (abs (- b a)))

;; ----------------------------------------------

(define-sort Temperature () Real)

(declare-datatypes ()
  ((Range
    (range (range-a Temperature) (range-b Temperature)))))

(define-fun range? ((R Range)) Bool
  (<= (range-a R) (range-b R)))

(define-fun singleton ((T Temperature)) Range
  (range T T))

(define-fun range-avg ((R Range)) Temperature
  (avg (range-a R) (range-b R)))

(define-fun range-distance-from ((T Temperature) (R Range)) Real
  (distance T (constrain (range-a R) (range-b R) T)))

;; ----------------------------------------------

(define-fun shared-range ((T Temperature) (X Range) (Y Range)) Range
  (let ((a (max (range-a X) (range-a Y)))
        (b (min (range-b X) (range-b Y))))
    ; If the comfortable-ranges overlap:
    (if (<= a b)
      ; take that overlapping region.
      (range a b)
      ; Otherwise one range is lower, and one range is higher,
      ; with a gap in the middle:
      ; take the temperature within the gap closest to the
      ; default temperature.
      (singleton (constrain b a T)))))

;; sr-fair-commutative
(define-fun sr-fair-commutative ((T Temperature) (X Range) (Y Range)) Bool
  (=> (and (range? X) (range? Y))
      (= (shared-range T X Y)
         (shared-range T Y X))))
;; unsat means it didn't find any counterexamples
(push)
  (declare-const T1 Temperature)
  (declare-const X1 Range)
  (declare-const Y1 Range)
  ; assert the negation so that a SAT solution
  ; would be a counterexample
  (assert (not (sr-fair-commutative T1 X1 Y1)))
  (check-sat)
(pop)

;; sr-associative
(define-fun sr-associative ((T Temperature) (X Range) (Y Range) (Z Range)) Bool
  (=> (and (range? X)
           (range? Y)
           (range? Z))
      (= (shared-range T (shared-range T X Y) Z)
         (shared-range T X (shared-range T Y Z)))))
;; unsat means it didn't find any counterexamples
(push)
  (declare-const T2 Temperature)
  (declare-const X2 Range)
  (declare-const Y2 Range)
  (declare-const Z2 Range)
  ; assert the negation
  (assert (not (sr-associative T2 X2 Y2 Z2)))
  (check-sat)
(pop)

;; ----------------------------------------------

(define-fun shared-temperature ((T Temperature) (X Range) (Y Range)) Temperature
  (range-avg (shared-range T X Y)))

;; st-fair-commutative
(define-fun st-fair-commutative ((T Temperature) (X Range) (Y Range)) Bool
  (=> (and (range? X) (range? Y))
      (= (shared-temperature T X Y)
         (shared-temperature T Y X))))
;; unsat means it didn't find any counterexamples
(push)
  (declare-const T3 Temperature)
  (declare-const X3 Range)
  (declare-const Y3 Range)
  ; assert the negation
  (assert (not (st-fair-commutative T3 X3 Y3)))
  (check-sat)
(pop)

;; st-as-good-as-any-alternative-in-total
(define-fun st-as-good-as-any-alternative-in-total ((T Temperature) (X Range) (Y Range) (alt Temperature)) Bool
  (=> (and (range? X) (range? Y))
      (let ((shared (shared-temperature T X Y)))
        (<=
         (+ (range-distance-from shared X) (range-distance-from shared Y))
         (+ (range-distance-from alt X) (range-distance-from alt Y))))))
;; unsat means it didn't find any counterexamples
(push)
  (declare-const T4 Temperature)
  (declare-const X4 Range)
  (declare-const Y4 Range)
  (declare-const alt4 Temperature)
  ; assert the negation
  (assert (not (st-as-good-as-any-alternative-in-total T4 X4 Y4 alt4)))
  (check-sat)
(pop)

;; st-no-advantage-to-lying
(define-fun st-no-advantage-to-lying ((T Temperature) (X Range) (X-lie Range) (Y Range)) Bool
  (=> (and (range? X) (range? X-lie) (range? Y))
      (<=
       (range-distance-from (shared-temperature T X Y) X)
       (range-distance-from (shared-temperature T X-lie Y) X))))
;; unsat means it didn't find any counterexamples
(push)
  (declare-const T5 Temperature)
  (declare-const X5 Range)
  (declare-const Xlie5 Range)
  (declare-const Y5 Range)
  ; assert the negation
  (assert (not (st-no-advantage-to-lying T5 X5 Xlie5 Y5)))
  (check-sat)
(pop)
