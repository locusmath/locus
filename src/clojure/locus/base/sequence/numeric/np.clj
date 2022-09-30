(ns locus.base.sequence.numeric.np
  (:require [clojure.set]
            [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.numeric.natural :refer :all]
            [locus.base.logic.numeric.nms :refer :all]))

; Let N be the set of natural numbers, then its cartesian square N^2 is the product of the set of natural
; numbers with itself. We call elements of this set natural pairs, and we provide a partially ordered
; hierarchy of subsets of this set for our set theoretic ontology.
(def natural-pair?
  (intersection
    size-two-seq?
    (partial every? natural-number?)))

(def equal-natural-pair?
  (intersection
    equal-size-two-seq?
    (partial every? natural-number?)))

(def distinct-natural-pair?
  (intersection
    distinct-size-two-seq?
    (partial every? natural-number?)))

(def positive-integer-pair?
  (intersection
    size-two-seq?
    (partial every? natural-number?)))

(def coprime-positive-integers?
  (intersection
    positive-integer-pair?
    (fn [[a b]]
      (= 1 (gcd a b)))))

(def natural-successor?
  (intersection
    natural-pair?
    (fn [[a b]]
      (= b (inc a)))))

(def natural-predecessor?
  (intersection
    natural-pair?
    (fn [[a b]]
      (= a (inc b)))))

(def near-natural-number?
  (intersection
    natural-pair?
    (fn [[a b]]
      (<= (int (Math/abs (- a b))) 1))))

; Properties ontology
(defn !=natural-pairs
  [a b]

  (and (natural-pair? a)
       (natural-pair? b)
       (not= a b)))

(defn !=natural-distance
  [p q]

  (and
    (natural-pair? p)
    (natural-pair? q)
    (not= (int (Math/abs (- (first p) (second p))))
          (int (Math/abs (- (first q) (second q)))))))

(defn !=natural-order
  [p q]

  (and
    (natural-pair? p)
    (natural-pair? q)
    (not= (compare (first p) (second p))
          (compare (first q) (second q)))))

(defn !=natural-difference
  [p q]

  (and
    (natural-pair? p)
    (natural-pair? q)
    (not= (- (first p) (second p))
          (- (first q) (second q)))))
