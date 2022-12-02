(ns locus.elementary.semigroup.monoid.arithmetic
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.numeric.natural :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.group-with-zero :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.elementary.semigroup.monoid.object Monoid)
           (locus.elementary.group.core.object Group)
           (locus.elementary.semigroup.core.object Semigroup)
           (locus.elementary.semigroup.monoid.group_with_zero GroupWithZero)))

; This file consists of a wide variety of semigroups that are of use in
; ring theory and related fields. In particular, we implement a number of
; additive and multiplicative semigroups of rings and semirings.

; Special semigroups
(def positive-integer-addition
  (Semigroup.
    positive-integer?
    (fn [[a b]]
      (+ a b))))

(def positive-integer-multiplication
  (Monoid.
    positive-integer?
    (fn [[a b]] (* a b))
    1))

; Maximum and minimum monoids
(defn max-monoid
  [n]

  (Monoid.
    (->Upto n)
    (fn [[a b]] (max a b))
    0))

(defn min-monoid
  [n]

  (Monoid.
    (->Upto n)
    (fn [[a b]] (min a b))
    (dec n)))

(defn power-set-union-monoid
  [coll]

  (->Monoid (->PowerSet coll) (fn [[a b]] (union a b)) #{}))

(defn power-set-intersection-monoid
  [coll]

  (->Monoid (->PowerSet coll) (fn [[a b]] (intersection a b)) coll))

; Composition of morphism subsets
(defn compose-sets-of-morphisms
  [category m1 m2]

  (set
    (for [[a b] (cartesian-product m1 m2)
          :when (composable-elements? category a b)]
      (category [a b]))))

(defn semigroup-of-sets-of-morphisms
  [category]

  (->Semigroup
    (->PowerSet (morphisms category))
    (fn [[a b]]
      (compose-sets-of-morphisms category a b))))

; Modular arithmetic semigroups
(defn modular-addition
  [n]

  (Group.
    (->Upto n)
    (fn [[a b]]
      (mod (+ a b) n))
    0
    (fn [x]
      (if (zero? x)
        0
        (- n x)))))

(defn modular-multiplication
  [n]

  (Monoid.
    (->Upto n)
    (fn [[a b]]
      (mod (* a b) n))
    1))

; Addition and multiplication monoids of essential semirings
; These include nn,zz,qq, and qt the most basic examples
; of semirings, rings, fields, and semifields
(def natural-multiplication
  (Monoid.
    natural-number?
    (fn [[a b]] (* a b))
    1))

(def natural-addition
  (Monoid.
    natural-number?
    (fn [[a b]] (+ a b))
    0))

(def integer-addition
  (Group.
    integer?
    (fn [[a b]] (+ a b))
    0
    (fn [x]
      (- x))))

(def integer-multiplication
  (Monoid.
    integer?
    (fn [[a b]] (* a b))
    1))

; Arithmetical semigroups of semifields
(def rational-addition
  (Group.
    rational?
    (fn [[a b]] (+ a b))
    0
    (fn [x] (- x))))

(def rational-multiplication
  (GroupWithZero.
    rational?
    (fn [[a b]] (* a b))
    1
    (fn [i]
      (if (zero? i) i (/ i)))
    0))

(def nonnegative-rational-addition
  (Monoid.
    nonnegative-rational-number?
    (fn [[a b]] (+ a b))
    0))

(def nonnegative-rational-multiplication
  (GroupWithZero.
    nonnegative-rational-number?
    (fn [[a b]] (* a b))
    1
    (fn [i]
      (if (zero? i) i (/ i)))
    0))

