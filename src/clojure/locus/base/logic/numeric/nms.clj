(ns locus.base.logic.numeric.nms
  (:require [clojure.set]
            [locus.base.logic.core.set :refer :all]
            [locus.base.logic.numeric.sig :refer :all])
  (:import (locus.base.logic.core.set Upto)))

; This file provides a basic ontology of additive partitions into classes, as well as a special
; ontology of other classes of multisets of natural numbers. We also provide a property ontology
; describing the partially ordered hierarchy of properties of multisets of natural numbers
; such as their sum, cardinality and signature.

; Cardinalities multiset
(defn cardinalities
  [coll]

  (multiset (map count coll)))

(defn power-cardinalities
  [n]

  (apply
   add
   (map
    (fn [i]
      (repeat-multiset (binomial-coefficient n i) i))
    (range (inc n)))))

; Natural universals
(defn natural-set?
  [coll]

  (and
   (universal? coll)
   (every? natural-number? coll)))

(defn natural-interval?
  [coll]

  (and
   (universal? coll)
   (or
    (= (count coll) 0)
    (let [min-value (apply min coll)
          max-value (apply max coll)]
      (= coll (set (range min-value (inc max-value))))))))

(defn positive-natural-range?
  [coll]

  (and
    (universal? coll)
    (= coll (set (range 1 (inc (count coll)))))))

; Natural ranges
(defmulti natural-range? type)

(defmethod natural-range? Upto
  [x] true)

(defmethod natural-range? :default
  [coll]

  (and
   (universal? coll)
   (= coll (set (range (count coll))))))

; Classes of natural multisets
(defn natural-multiset?
  [coll]

  (and
   (multiset? coll)
   (every? natural-number? coll)))

(defn additive-partition?
  [coll]

  (and
   (multiset? coll)
   (every? positive-integer? coll)))

; Additive partitions and additive divisions
(def equal-natural-multiset?
  (intersection
   equal-multiset?
   natural-multiset?))

(defn additive-division?
  [coll]

  (and
   (equal-multiset? coll)
   (every? positive-integer? coll)))

(defn self-conjugate-additive-partition?
  [coll]

  (and
   (additive-partition? coll)
   (= coll (conjugate-partition coll))))

(def distinct-additive-partition?
  (intersection
   universal?
   additive-partition?))

; Limited sizes
(def singular-natural-multiset?
  (intersection
   singular-universal?
   natural-multiset?))

(def size-two-natural-multiset?
  (intersection
   size-two-multiset?
   natural-multiset?))

(def size-three-natural-multiset?
  (intersection
   size-three-multiset?
   natural-multiset?))

(def size-four-natural-multiset?
  (intersection
   size-four-multiset?
   natural-multiset?))

(def singular-additive-partition?
  (intersection
   singular-universal?
   additive-partition?))

(def size-two-additive-partition?
  (intersection
   size-two-multiset?
   additive-partition?))

(def size-three-additive-partition?
  (intersection
   size-three-multiset?
   additive-partition?))

(def size-four-additive-partition?
  (intersection
   size-four-multiset?
   additive-partition?))

; Max values
(defn max-value-four-natural-multiset?
  [coll]

  (and
   (natural-multiset? coll)
   (every? (fn [i] (<= i 4)) coll)))

(defn max-value-three-natural-multiset?
  [coll]

  (and
   (natural-multiset? coll)
   (every? (fn [i] (<= i 3)) coll)))

(defn max-value-two-natural-multiset?
  [coll]

  (and
   (natural-multiset? coll)
   (every? (fn [i] (<= i 2)) coll)))

(defn logical-natural-multiset?
  [coll]

  (and
   (natural-multiset? coll)
   (every? (fn [i] (<= i 1)) coll)))

(defn max-value-two-additive-partition?
  [coll]

  (and
   (additive-partition? coll)
   (every? (fn [i] (<= i 2)) coll)))

(defn max-value-three-additive-partition?
  [coll]

  (and
   (additive-partition? coll)
   (every? (fn [i] (<= i 3)) coll)))

(defn max-value-four-additive-partition?
  [coll]

  (and
   (additive-partition? coll)
   (every? (fn [i] (<= i 4)) coll)))

; Distinction relations
(defn !=natural-multiset
  [a b]

  (and
   (natural-multiset? a)
   (natural-multiset? b)
   (not= a b)))

(defn !=natural-multiset-signature
  [a b]

  (and
   (natural-multiset? a)
   (natural-multiset? b)
   (not= (signature a) (signature b))))

(defn !=natural-multiset-count
  [a b]

  (and
    (natural-multiset? a)
    (natural-multiset? b)
    (not= (count a) (count b))))

(defn !=natural-multiset-sum
  [a b]

  (and
   (natural-multiset? a)
   (natural-multiset? b)
   (not= (apply + a) (apply + b))))
