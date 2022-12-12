(ns locus.set.logic.numeric-sequence.ac
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.numeric.ap :refer :all]))

; The additive partitions system provides support for partitioning natural numbers into unordered collections
; of positive integers. In this file, we generalize that concept to ordered partitions of natural numbers.

; This is an attempt to get an additive composition from a natural system
(defn compute-differences
  [coll]

  (let [sorted-coll (sort < coll)]
    (map
      (fn [i]
        (if (zero? i)
          (inc (nth sorted-coll i))
          (- (nth sorted-coll i) (nth sorted-coll (dec i)))))
      (range (count sorted-coll)))))

(defn complete-differences
  [coll n]

  (let [sum (apply + coll)]
    (cons (- n sum) coll)))

(defn get-composition
  [coll n]

  (let [initial-differences (compute-differences coll)]
    (complete-differences initial-differences n)))

(defn restricted-compositions
  [n k]

  (if (zero? n)
    '()
    (map
      #(get-composition % n)
      (selections (set (range (dec n))) (dec k)))))

(defn all-compositions
  [n]

  (if (zero? n)
    '()
    (map
      #(get-composition % n)
      (power-set (set (range (dec n)))))))