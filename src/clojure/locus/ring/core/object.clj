(ns locus.ring.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.ring.core.arithmetic :as arith]
            [locus.ring.core.protocols :refer :all])
  (:import (locus.elementary.group.core.object Group)
           (locus.elementary.semigroup.core.object Semigroup)))

; Rings are the most useful objects of arithmetic because of their relationship
; to ideals. The unique role of rings requires that we offer special support
; for them in our computer algebra system.
(deftype Ring [elems add mul]
  ConcreteObject
  (underlying-set [this] elems))

(derive Ring :locus.ring.core.protocols/ring)

(defmethod additive-semigroup Ring
  [^Ring ring]

  (.add ring))

(defmethod multiplicative-semigroup Ring
  [^Ring ring]

  (.mul ring))

(defmethod make-ring :locus.elementary.function.core.protocols/group
  [a b]

  (Ring.
    (underlying-set a)
    a
    b))

; The fundamental ring of integers and its quotients
(def zz
  (make-ring
    integer-addition
    integer-multiplication))

(defn zn
  [n]

  (make-ring
    (modular-addition n)
    (modular-multiplication n)))

(defn nz
  [n]

  (let [coll (->Universal
               (fn [i]
                 (and
                   (natural-number? i)
                   (divides? n i))))]
    (Ring.
      coll
      (Group.
        coll
        (fn [[a b]] (+ a b))
        0
        (fn [i] (- i)))
      (->Semigroup
        coll
        (fn [[a b]] (* a b))))))

; The unique prime field of characteristic zero
(def qq
  (make-ring rational-addition rational-multiplication))

; Products in the category of rings
(defmethod product Ring
  [& rings]

  (->Ring
    (apply product (map underlying-set rings))
    (apply product (map additive-semigroup rings))
    (apply product (map multiplicative-semigroup rings))))

; Boolean rings are direct products of the finite field of two elements
(defn boolean-ring
  [n]

  (let [size (int (Math/pow 2 n))]
    (make-ring
      (Group.
        (seqable-interval 0 size)
        (fn [[a b]]
          (bit-xor a b))
        0
        (fn [n]
          (bit-xor (dec size) n)))
      (Semigroup.
        (seqable-interval 0 size)
        (fn [[a b]]
          (bit-and a b))))))

; The subalgebra lattice of a ring
(defn subring?
  [ring coll]

  (and
    (subgroup? (additive-semigroup ring) coll)
    (subsemigroup? (multiplicative-semigroup ring) coll)))

(defn subrings
  [ring]

  (let [mul (multiplicative-semigroup ring)]
    (set
      (filter
        (fn [coll]
          (subsemigroup? mul coll))
        (all-subgroups (additive-semigroup ring))))))

(defmethod sub Ring
  [ring]

  (->Lattice (subrings ring) union intersection))

(defn restrict-ring
  [ring coll]

  (Ring.
    coll
    (restrict-semigroup (additive-semigroup ring) coll)
    (restrict-semigroup (multiplicative-semigroup ring) coll)))

; Compute the nilradical of a ring
(defn nilradical
  [ring]

  (set (nilpotent-elements (multiplicative-semigroup ring))))

; Get all ideals of a ring
(defn ring-ideal?
  [ring coll]

  (and
    (subgroup? (additive-semigroup ring) coll)
    (two-sided-ideal? (multiplicative-semigroup ring) coll)))

(defn ring-ideals
  [ring]

  (let [mul (multiplicative-semigroup ring)]
    (set
      (filter
        (fn [coll]
          (two-sided-ideal? mul coll))
        (all-subgroups (additive-semigroup ring))))))

(defmethod con Ring
  [ring]

  (->Lattice (ring-ideals ring) union intersection))

(defn ring-ideal->congruence
  [ring coll]

  (normal-subgroup->congruence (additive-semigroup ring) coll))

(defn quotient-ring
  [ring partition]

  (Ring.
    partition
    (quotient-semigroup ring partition)
    (quotient-semigroup ring partition)))

(defn quotient-ring-by-ideal
  [ring ideal]

  (quotient-ring ring (ring-ideal->congruence ring ideal)))

; The left and right ideals of noncommutative algebra
(defn ring-left-ideal?
  [ring ideal]

  (and
    (subgroup? (additive-semigroup ring) ideal)
    (left-ideal? (multiplicative-semigroup ring) ideal)))

(defn ring-left-ideals
  [ring]

  (set
    (filter
      (fn [coll]
        (ring-left-ideal? ring coll))
      (power-set (underlying-set ring)))))

(defn ring-right-ideal?
  [ring ideal]

  (and
    (subgroup? (additive-semigroup ring) ideal)
    (right-ideal? (multiplicative-semigroup ring) ideal)))

(defn ring-right-ideals
  [ring]

  (set
    (filter
      (fn [coll]
        (ring-right-ideal? ring coll))
      (power-set (underlying-set ring)))))

; Prime ideals in rings are determined by their multiplicative subsemigroups
(defn ring-prime-ideal?
  [ring coll]

  (and
    (subgroup? (additive-semigroup ring) coll)
    (semigroup-prime-ideal? (multiplicative-semigroup ring) coll)))

(defn spec
  [ring]

  (let [mul (multiplicative-semigroup ring)]
    (set
      (filter
        (fn [coll]
          (semigroup-prime-ideal? mul coll))
        (proper-subgroups (additive-semigroup ring))))))

; The krull dimension of any finite ring is zero
; So this computation is only useful in cases where the
; prime spectrum of a commutative ring can be computed otherwise.
(defn krull-dimension
  [ring]

  (dec (family-height (spec ring))))




