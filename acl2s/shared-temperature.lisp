; How to run from Emacs:
;   0. Split window with "control-x 2"
;   1. In the repl window, "M-x run-acl2"
;   2. In the repl window, "control-t c"
;   3. Back in the file, "control-t control-e", then enter
;   4. Move the cursor to the next S-expression in the file
;   repeat steps (3) and (4)
; For step (4), "M-a" and "M-e" can help

;; ---------------------------------------------------------

(defconst *else* t)

(defunc avg (a b)
  :input-contract (and (rationalp a)
                       (rationalp b))
  :output-contract (rationalp (avg a b))
  (/ (+ a b) 2))

(defunc constrain (a b x)
  :input-contract (and (rationalp a)
                       (rationalp b)
                       (rationalp x)
                       (<= a b))
  :output-contract (rationalp (constrain a b x))
  (max a (min b x)))

(defdata temperature rational)

(defdata pairof-temperature (cons temperature temperature))

;; A Range is a (range a b) such that:
;;  * a : temperature
;;  * b : temperature
;;  * (<= a b)
(defunc rangep (v)
  :input-contract t
  :output-contract (booleanp (rangep v))
  (and (pairof-temperaturep v)
       (<= (car v) (cdr v))))

(defunc range (a b)
  :input-contract (and (temperaturep a)
                       (temperaturep b)
                       (<= a b))
  :output-contract (rangep (range a b))
  (cons a b))
(defunc range-a (r)
  :input-contract (rangep r)
  :output-contract (temperaturep (range-a r))
  (car r))
(defunc range-b (r)
  :input-contract (rangep r)
  :output-contract (temperaturep (range-b r))
  (cdr r))


(defunc singleton (temp)
  :input-contract (temperaturep temp)
  :output-contract (rangep (singleton temp))
  (range temp temp))

(defunc range-avg (r)
  :input-contract (rangep r)
  :output-contract (temperaturep (range-avg r))
  (let ((a (range-a r))
        (b (range-b r)))
    (avg a b)))

(defunc range-distance-from (Te R)
  :input-contract (and (temperaturep Te)
                       (rangep R))
  :output-contract (rationalp (range-distance-from Te R))
  (let ((a (range-a R))
        (b (range-b R)))
    (cond ((< Te a)  (- a Te))
          ((< b Te)  (- Te b))
          (*else*    0))))

;; ---------------------------------------------------------

(defunc shared-range (Te X Y)
  :input-contract (and (temperaturep Te)
                       (rangep X)
                       (rangep Y))
  :output-contract (rangep (shared-range Te X Y))
  (let ((X-a (range-a X))
        (X-b (range-b X))
        (Y-a (range-a Y))
        (Y-b (range-b Y)))
    (let ((a (max X-a Y-a))
          (b (min X-b Y-b)))
      (cond 
       ; If the comfortable-ranges overlap:
       ((<= a b)
        ; take that overlapping region.
        (range a b))
       ; Otherwise one range is lower, and one range is higher,
       ; with a gap in the middle:
       (*else*
        ; take the temperature within the gap closest to the
        ; default temperature.
        (singleton (constrain b a Te)))))))

(defthm sr-fair-commutative
  (implies (and (temperaturep Te)
                (rangep A)
                (rangep B))
           (equal (shared-range Te A B)
                  (shared-range Te B A))))

(defthm sr-associative
  (implies (and (temperaturep Te)
                (rangep A)
                (rangep B)
                (rangep C))
           (equal (shared-range Te (shared-range Te A B) C)
                  (shared-range Te A (shared-range Te B C)))))

;; ---------------------------------------------------------

(defunc shared-temperature (Te X Y)
  :input-contract (and (temperaturep Te)
                       (rangep X)
                       (rangep Y))
  :output-contract (temperaturep (shared-temperature Te X Y))
  (range-avg (shared-range Te X Y)))

(defthm st-fair-commutative
  (implies (and (temperaturep Te)
                (rangep A)
                (rangep B))
           (equal (shared-temperature Te A B)
                  (shared-temperature Te B A))))

(defthm st-as-good-as-any-alternative-in-total
  (implies 
   (and (temperaturep Te)
        (rangep A)
        (rangep B)
        (temperaturep alt))
   (let ((shared (shared-temperature Te A B)))
     (<=
      (+ (range-distance-from shared A) (range-distance-from shared B))
      (+ (range-distance-from alt A) (range-distance-from alt B))))))

(defthm st-no-advantage-to-lying
  (implies (and (temperaturep Te)
                (rangep A)
                (rangep A-lie)
                (rangep B))
           (<= (range-distance-from (shared-temperature Te A B) A)
               (range-distance-from (shared-temperature Te A-lie B) A))))

;; ---------------------------------------------------------

