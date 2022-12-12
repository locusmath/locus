(ns locus.set.logic.numeric-sequence.onms
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.numeric.natural :refer :all]
            [locus.set.logic.sequence.object :refer :all]))

; This file defines the basic ontology of ordered additive partitions as well as other
; ordered sequences of natural numbers.

(def natural-seq?
  (intersection
   seq?
   (partial every? natural-number?)))

(def logical-seq?
  (intersection
   seq?
   (partial
    every?
    (fn [i]
      (and
       (natural-number? i)
       (<= 0 i 1))))))

(def additive-composition?
  (intersection
   seq?
   (partial every? positive-integer?)))

(def max-value-two-additive-composition?
  (intersection
   natural-seq?
   (partial every? (fn [i] (<= 1 i 2)))))

(defn monotone-natural-seq?
  [coll]

  (and
   (natural-seq? coll)
   (= coll (sort <= coll))))

(defn inverse-monotone-natural-seq?
  [coll]
  
  (and
   (natural-seq? coll)
   (= coll (sort <= coll))))

(def distinct-monotone-natural-seq?
  (intersection
   distinct-seq?
   monotone-natural-seq?))

(def distinct-inverse-monotone-natural-seq?
  (intersection
   distinct-seq?
   inverse-monotone-natural-seq?))

(defn endoseq?
  [coll]

  (let [n (count coll)]
    (every?
     (fn [i]
       (< i n))
     coll)))

(def permutation-seq?
  (intersection
   distinct-seq?
   endoseq?))

(defn lattice-path?
  [coll]

  (every?
   (fn [i]
     (<= (nth coll i) i))
   (range (count coll))))

(def monotone-lattice-path?
  (intersection
   lattice-path?
   monotone-natural-seq?))

; Pythagoreon triple
(defn pythagorean-triple?
  [coll]

  (and
   (additive-composition? coll)
   (letfn [(square [n] (* n n))]
     (= (square (nth coll 2))
        (+ (square (first coll))
           (square (second coll)))))))

; Lexicographic orderings
(defn frontlex-successor?
  [a b]

  (or
   (and (empty? a) (empty? b))
   (< (first a) (first b))
   (and (= (first a) (first b))
        (frontlex-successor? (rest a) (rest b)))))

(defn backlex-successor?
  [a b]

  (or
   (and (empty? a) (empty? b))
   (< (last a) (last b))
   (and (= (last a) (last b))
        (backlex-successor? (butlast a) (butlast b)))))


