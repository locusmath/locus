(ns locus.number.sequence.all
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.logic.numeric.natural :refer [factors]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]))

; Here we define a special number sequence data type for dealing with rings
; of sequences over number fields.
(deftype NumberSequence [func]
  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  clojure.lang.Seqable
  (seq [this] (map func (range))))

(defmethod negate NumberSequence
  [seq]

  (NumberSequence.
    (fn [n]
      (- (seq n)))))

(defmethod add [NumberSequence NumberSequence]
  [a b]

  (NumberSequence.
    (fn [i]
      (+ (a i) (b i)))))

(defmethod multiply [NumberSequence NumberSequence]
  [a b]

  (NumberSequence.
    (fn [i]
      (* (a i) (b i)))))

(defmethod reciprocal NumberSequence
  [seq]

  (NumberSequence.
    (fn [n]
      (/ n))))

(defmethod compose* NumberSequence
  [a b]

  (NumberSequence.
    (fn [n]
      (a (b n)))))

; Get the consecutive sums, differences, products and divisions
(defn consecutive-differences
  [f]

  (NumberSequence.
    (fn [n]
      (if (zero? n)
        (f n)
        (- (f n) (f (dec n)))))))

(defn consecutive-divisions
  [f]

  (NumberSequence.
    (fn [n]
      (if (zero? n)
        (f n)
        (/ (f n) (f (dec n)))))))

(defn consecutive-sums
  [f]

  (NumberSequence.
    (fn [n]
      (apply + (map f (range (inc n)))))))

(defn consecutive-products
  [f]

  (NumberSequence.
    (fn [n]
      (apply * (map f (range (inc n)))))))

; Inverse sequences
(defn preceding-elements
  [func current-index n]

  (if (< n (func current-index))
    (list)
    (cons (func current-index) (preceding-elements func (inc current-index) n))))

(defn get-inverse-value
  [func n]

  (let [elems (preceding-elements func 0 n)]
    (if (empty? elems)
      0
      (dec (count elems)))))

(defn inverse-sequence
  [func]

  (NumberSequence.
    (fn [n]
      (get-inverse-value func n))))

; Functions for creating integer sequences
(defn periodic-sequence
  [initial-segment repeating-elements]

  (NumberSequence.
    (fn [n]
      (if (< n (count initial-segment))
        (nth initial-segment n)
        (nth repeating-elements (mod (- n (count initial-segment)) (count repeating-elements)))))))

(defn linear-growth-integer-sequence
  [x]

  (NumberSequence.
    (fn [n]
      (int (Math/floor (* x n))))))

; Nth negative integer
(def nth-negative-integer
  (NumberSequence.
    (fn [n] (- (inc n)))))

(def nth-negative-odd
  (NumberSequence.
    (fn [n]
      (- (inc (* 2 n))))))

(def nth-nonpositive-even
  (NumberSequence.
    (fn [n]
      (- (* 2 n)))))

(def nth-negative-even
  (NumberSequence.
    (fn [n]
      (- (* 2 (inc n))))))

(def nth-nonpositive-integer
  (NumberSequence.
    (fn [n] (- n))))

(def nth-natural-number
  (NumberSequence.
    (fn [n] n)))

(def nth-positive-integer
  (NumberSequence.
    (fn [n] (+ n 1))))

(def nth-even
  (NumberSequence.
    (fn [n] (* 2 n))))

(def nth-positive-even
  (NumberSequence.
    (fn [n] (* 2 (inc n)))))

(def nth-odd
  (NumberSequence.
    (fn [n] (inc (* 2 n)))))

; The fundamental polygonal number sequences
(def nth-square
  (NumberSequence.
    (fn [n]
      (* n n))))

(def nth-pronic-number
  (NumberSequence.
    (fn [n]
      (* n (inc n)))))

(def nth-triangular-number
  (NumberSequence.
    (fn [n]
      (/ (* n (inc n))
         2))))

(def nth-pentagonal-number
  (NumberSequence.
    (fn [n]
      (/ (- (* 3 n n) n)
         2))))

(def nth-hexagonal-number
  (NumberSequence.
    (fn [n]
      (- (* 2 n n) n))))

(def nth-octagonal-number
  (NumberSequence.
    (fn [n]
      (/ (- (* 5 n n) (* 3 n))
         2))))

(def nth-nonagonal-number
  (NumberSequence.
    (fn [n]
      (/ (* n (- (* 7 n) 5))
         2))))

(def nth-decagonal-number
  (NumberSequence.
    (fn [n]
      (- (* 4 n n) (* 3 n)))))

; Centered figurate numbers
(def nth-centered-triangular-number
  (NumberSequence.
    (fn [n]
      (inc
        (/ (* 3 n (dec n))
           2)))))

(def nth-centered-square-number
  (NumberSequence.
    (fn [n]
      (+ (* n n)
         (* (dec n) (dec n))))))

(def nth-centered-pentagonal-number
  (NumberSequence.
    (fn [n]
      (/ (+ (* 5 n n) (- (* 5 n)) 2)
         2))))

(def nth-centered-hexagonal-number
  (NumberSequence.
    (fn [n]
      (+ (* 3 n n)
         (* -3 n)
         1))))

(def nth-centered-heptagonal-number
  (NumberSequence.
    (fn [n]
      (/ (+ (* 7 n n) (* -7 n) 2)
         2))))

(def nth-centered-octagonal-number
  (NumberSequence.
    (fn [n]
      (+ (* 4 n n) (* 4 n) 1))))

(def nth-centered-nonagonal-number
  (NumberSequence.
    (fn [n]
      (/ (* (- (* 3 n) 2)
            (- (* 3 n) 1))
         2))))

(def nth-centered-decagonal-number
  (NumberSequence.
    (fn [n]
      (+ (* 5 n n)
         (* 5 n)
         1))))

; Three dimensional numbers
(def nth-square-pyramidal-number
  (NumberSequence.
    (fn [n]
      (+ (/ (* n n n) 3)
         (/ (* n n) 2)
         (/ n 6)))))

; Extra number sequences
(def nth-tetrahedral-number
  (NumberSequence.
    (fn [n]
      (/ (* n (+ n 1) (+ n 2))
         6))))

(def nth-cube
  (NumberSequence.
    (fn [n]
      (* n n n))))

; Centered tetrahedral numbers
(def nth-centered-tetrahedral-number
  (NumberSequence.
    (fn [n]
      (/ (* (+ (* 2 n) 1)
            (+ (* n n) n 3))
         3))))

(def nth-centered-cube-number
  (NumberSequence.
    (fn [n]
      (+ (nth-cube n)
         (nth-cube (inc n))))))

; Pentatope numbers
(def nth-pentatope-number
  (NumberSequence.
    (fn [n]
      (/ (* n (+ n 1) (+ n 2) (+ n 3))
         24))))

; Squared triangular numbers are sums of cubes
(def nth-squared-triangular-number
  (NumberSequence.
    (fn [n]
      (nth-square
        (nth-triangular-number n)))))

; Numbers growing at an exponential rate
(def nth-binary-number
  (NumberSequence.
    (fn [n]
      (apply * (repeat n 2N)))))

(def nth-fibonacci-number
  (NumberSequence.
    (fn fib [n]
      (if (< n 2)
        1
        (+ (fib (- n 1)) (fib (- n 2)))))))

(def nth-factorial
  (NumberSequence.
    (fn [n]
      (locus.base.logic.core.set/factorial n))))

; The sum of divisors function
(def sum-of-divisors
  (NumberSequence.
    (fn [n]
      (apply + (divisors n)))))

(def catalan-number
  (NumberSequence.
    (fn [n]
      (/ (factorial (* 2 n))
         (* (factorial n) (factorial (inc n)))))))

; Rational numbers
; Continued fractions are needed
(def nth-unit-fraction
  (NumberSequence.
    (fn [n]
      (/ (inc n)))))

(def nth-fibonacci-ratio
  (NumberSequence.
    (fn [n]
      (/ (nth-fibonacci-number (+ n 1))
         (nth-fibonacci-number n)))))

(def nth-factorial-reciprocal
  (NumberSequence.
    (fn [n]
      (/ (nth-factorial n)))))

(def nth-euler-ratio
  (NumberSequence.
    (fn [n]
      (apply
        +
        (map
          (fn [i]
            (/ (factorial i)))
          (range n))))))

(def nth-basel-ratio
  (NumberSequence.
    (fn [n]
      (apply
        +
        (map
          (fn [i]
            (/ (nth-square i)))
          (range 1 n))))))

; Continued fractions
(defn continued-fraction-value
  [coll]

  (if (= (count coll) 1)
    (first coll)
    (+ (first coll) (/ (continued-fraction-value (rest coll))))))

(defn continued-fraction-sequence
  [coll]

  (NumberSequence.
    (fn [n]
      (continued-fraction-value (take (inc n) coll)))))

(def nth-root-ratio
  (NumberSequence.
    (fn [n]
      (continued-fraction-value
        (map
          (fn [i]
            (if (zero? i)
              1
              2))
          (range (inc n)))))))















