(ns locus.algebra.commutative.monoid.arithmetic
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.numeric.natural :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.monoid.group-with-zero :refer :all]
            [locus.algebra.commutative.monoid.object :refer :all]
            [locus.algebra.commutative.monoid.group-with-zero :refer :all]
            [locus.algebra.abelian.group.object :refer :all])
  (:import (locus.algebra.commutative.semigroup.object CommutativeSemigroup)
           (locus.algebra.commutative.monoid.object CommutativeMonoid)
           (locus.algebra.abelian.group.object CommutativeGroup)))

; The unique infinite monogenic commutative semigroup
(def positive-integer-addition
  (CommutativeSemigroup.
    positive-integer?
    (fn [[a b]]
      (<= a b))
    (fn [[a b]]
      (+ a b))))

; The free commutative monoid on an infinite set of generators
(def positive-integer-multiplication
  (CommutativeMonoid.
    positive-integer?
    (fn [[a b]]
      (divides? (list a b)))
    (fn [[a b]] (* a b))
    1))

; Total order semilattices
(defn max-monoid
  [n]

  (CommutativeMonoid.
    (->Upto n)
    (fn [[a b]]
      (<= a b))
    (fn [[a b]] (max a b))
    0))

(defn min-monoid
  [n]

  (CommutativeMonoid.
    (->Upto n)
    (fn [[a b]]
      (<= b a))
    (fn [[a b]]
      (min a b))
    (dec n)))

; Power set semilattices
(defn power-set-union-monoid
  [coll]

  (->CommutativeMonoid
    (->PowerSet coll)
    superset?
    (fn [[a b]]
      (union a b))
    #{}))

(defn power-set-intersection-monoid
  [coll]

  (->CommutativeMonoid
    (->PowerSet coll)
    (fn [[a b]]
      (superset? (list b a)))
    (fn [[a b]]
      (intersection a b))
    coll))

; Modular arithmetic semigroups
(defn modular-addition
  [n]

  (->CommutativeGroup
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

  (CommutativeMonoid.
    (->Upto n)
    (fn [[a b]]
      (not
        (every?
          (fn [i]
            (not= (mod (* a i) n) b))
          (range n))))
    (fn [[a b]]
      (mod (* a b) n))
    1))

; Addition and multiplication monoids of essential semirings
; These include nn,zz,qq, and qt the most basic examples
; of semirings, rings, fields, and semifields
(def natural-multiplication
  (CommutativeMonoid.
    natural-number?
    (fn [[a b]]
      (divides? (list a b)))
    (fn [[a b]]
      (* a b))
    1))

(def natural-addition
  (CommutativeMonoid.
    natural-number?
    (fn [[a b]]
      (<= a b))
    (fn [[a b]]
      (+ a b))
    0))

(def integer-addition
  (CommutativeGroup.
    integer?
    (fn [[a b]]
      (+ a b))
    0
    (fn [x]
      (- x))))

(def integer-multiplication
  (CommutativeMonoid.
    integer?
    (fn [[a b]]
      (divides?
        (list
          (int (abs a))
          (int (abs b)))))
    (fn [[a b]]
      (* a b))
    1))

; Arithmetical semigroups of semifields
(def rational-addition
  (->CommutativeGroup
    rational?
    (fn [[a b]] (+ a b))
    0
    (fn [x] (- x))))

(def rational-multiplication
  (->CommutativeGroupWithZero
    rational?
    (fn [[a b]] (* a b))
    1
    (fn [i]
      (if (zero? i) i (/ i)))
    0))

(def nonnegative-rational-addition
  (CommutativeMonoid.
    nonnegative-rational-number?
    (fn [[a b]]
      (<= a b))
    (fn [[a b]] (+ a b))
    0))

(def nonnegative-rational-multiplication
  (->CommutativeGroupWithZero
    nonnegative-rational-number?
    (fn [[a b]] (* a b))
    1
    (fn [i]
      (if (zero? i) i (/ i)))
    0))