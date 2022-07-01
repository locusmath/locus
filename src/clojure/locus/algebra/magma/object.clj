(ns locus.algebra.magma.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; Let S be a set then a magma on S is simply a function of the form
; f : S^2 -> S. We consider magmas to be a special subcategory of the
; topos functions of this form. Each magma subobject produces a subfunction
; and each magma congruence produces a congruence of functions in the topos
; Sets^(->) of functions.
(deftype Magma [coll op]
  ConcreteObject
  (underlying-set [this] coll)

  ConcreteMorphism
  (inputs [this] (complete-relation coll))
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Magma :locus.elementary.function.core.protocols/structured-set)

; Display a magma
(defmethod display-table Magma
  [magma] (doseq [i (multiplication-table magma)] (prn i)))

; Convert certain objects into magmas
(defmulti to-magma type)

(defmethod to-magma :locus.elementary.function.core.protocols/semigroup
  [semigroup]

  (Magma. (underlying-set semigroup) (fn [pair] (semigroup pair))))

(defmethod to-magma SetFunction
  [func]

  (Magma. (outputs func) func))

; Create a magma by a table
(defn magma-by-table
  [coll]

  (let [n (count coll)]
    (Magma.
      (seqable-interval 0 n)
      (fn [[i j]]
        (nth (nth coll i) j)))))

; Special elements of magmas
(defn idempotents-of-magma
  [magma]

  (filter
    (fn [i]
      (= i (magma (list i i))))
    (underlying-set magma)))

; We can dualize any magma by reversing its ordering
(defmethod dual Magma
  [magma]

  (Magma.
    (underlying-set magma)
    (fn [pair] (magma (reverse pair)))))

(defmethod product Magma
  [& magmas]

  (Magma.
    (apply cartesian-product (map underlying-set magmas))
    (fn [[coll1 coll2]]
      (map
        (fn [i]
          ((nth magmas i) (list (nth coll1 i) (nth coll2 i))))
        (range (count magmas))))))

; Get if a given subset is a submagma
(defn submagma?
  [magma coll]

  (every?
    (fn [pair]
      (contains? coll (magma pair)))
    (cartesian-power coll 2)))

(defmethod sub Magma
  [magma]

  (->Lattice
    (set
      (filter
       (fn [coll]
         (submagma? magma coll))
       (power-set (underlying-set magma))))
    union
    intersection))

(defn restrict-magma
  [magma coll]

  (Magma. coll (.op magma)))

; Test if a given partition constitutes a congruence of the magma
(defn magma-congruence?
  [magma partition]

  (every?
    (fn [[coll1 coll2]]
      (equal-seq?
        (map
          (comp (partial projection partition) magma)
          (cartesian-product coll1 coll2))))
    (cartesian-power partition 2)))

(defmethod con Magma
  [magma]

  (->Lattice
    (set
      (filter
        (fn [partition]
          (magma-congruence? magma partition))
        (set-partitions (set (underlying-set magma)))))
    join-set-partitions
    meet-set-partitions))

(defn quotient-magma
  [magma partition]

  (Magma.
    partition
    (fn [[c1 c2]]
      (projection partition (magma (list (first c1) (first c2)))))))

; Ontology of magmas
(defn magma?
  [magma]

  (= (type magma) Magma))

(defn commutative-magma?
  [magma]

  (and
    (magma? magma)
    (every?
      (fn [pair]
        (= (magma pair) (magma (reverse pair))))
      (inputs magma))))

(defn idempotent-magma?
  [magma]

  (and
    (magma? magma)
    (every?
      (fn [i]
        (= (magma (list i i)) i))
      (underlying-set magma))))

