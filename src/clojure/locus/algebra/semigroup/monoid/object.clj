(ns locus.algebra.semigroup.monoid.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.copresheaf.bijection.core.morphism :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (locus.set.mapping.general.core.object SetFunction)
           (locus.algebra.semigroup.core.object Semigroup)))

; Monoids are single object concrete categories. As we often encounter subsets of
; monoids that don't have identity elements, we include monoids within a larger
; system that includes support for semigroups. In this file, we provide special
; support for monoids in hopes that by doing so we will have a better system
; of all around support for category theory for use in defining copresheaf topoi.

(deftype Monoid [elems op id]
  ; Monoids have underlying sets
  ConcreteObject
  (underlying-set [this] elems)

  ; Monoids are categories so they are structured unital quivers
  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (singular-unital-quiver elems 0 id))
  (identity-morphism-of [this obj] id)

  ; Every monoid is a function
  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj]
    (op obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Tagging monoids as semigroupoids
(derive Monoid :locus.set.copresheaf.structure.core.protocols/monoid)

; Convert semigroups to monoids
(defmulti to-monoid type)

(defmethod to-monoid Semigroup
  [^Semigroup semigroup]

  (let [identities (identity-elements semigroup)]
    (when (not (empty? identities))
      (Monoid.
        (underlying-set semigroup)
        (.op semigroup)
        (first identities)))))

(defmethod to-monoid Monoid
  [monoid] monoid)

(defmethod to-monoid SetFunction
  [func] (to-monoid (to-semigroup func)))

; create a monoid by a table
(defn monoid-by-table
  [coll]

  (to-monoid (semigroup-by-table coll)))

; Apply monoid
(defn apply-monoid
  [func coll]

  (if (empty? coll)
    (identity-element func)
    (apply-semigroup func coll)))

; Monogenic monoids
(defn monogenic-monoid
  [index period]

  (Monoid.
    (->Upto (+ index period))
    (fn [[a b]]
      (cond
        (zero? a) b
        (zero? b) a
        :else (monogenic-simplification index period (+ a b))))
    0))

; Group with zero
(defmulti group-with-zero (fn [coll func one inv zero] (type coll)))

; Make a trivial monoid with only a single element elem
(defn make-trivial-monoid
  [elem]

  (Monoid.
    #{elem}
    (fn [[a b]]
      elem)
    elem))

; The simple example of a trivial monoid
(def trivial-monoid
  (make-trivial-monoid 0))

; A monoid for the concatenation of strings
(defn as-concatenation-monoid
  [coll]

  (Monoid.
    coll
    (fn [[a b]]
      (str a b))
    ""))

(def string-concatenation-monoid
  (as-concatenation-monoid string?))

; This makes getting the identity element of a monoid easier
(defmethod identity-elements Monoid
  [sgrp]

  #{(.id sgrp)})

; Product operation for monoids
(defmethod product :locus.set.copresheaf.structure.core.protocols/monoid
  [& monoids]

  (Monoid.
    (apply cartesian-product (map underlying-set monoids))
    (apply semigroup-product-function monoids)
    (map identity-element monoids)))

; Subalgebra lattices of monoids
(defmethod sub :locus.set.copresheaf.structure.core.protocols/monoid
  [monoid]

  (Lattice.
    (identity-preserving-subsemigroups monoid)
    (comp (partial subsemigroup-closure monoid) union)
    intersection))

(defn restrict-monoid
  [^Monoid m, coll]

  (Monoid.
    coll
    (.op m)
    (.id m)))

; Congruence lattices of monoids
(defmethod con :locus.set.copresheaf.structure.core.protocols/monoid
  [monoid]

  (con (->Semigroup (underlying-set monoid) (.op monoid))))

(defn quotient-monoid
  [monoid partition]

  (Monoid.
    partition
    (fn [[c1 c2]]
      (projection partition (monoid (list (first c1) (first c2)))))
    (projection partition (first (identity-elements monoid)))))

; Adjoin an identity to a semigroup to a get a monoid
(defmethod adjoin-identity :default
  [semigroup]

  (Monoid.
    (cartesian-coproduct
      #{0}
      (underlying-set semigroup))
    (fn [[[i v] [j w]]]
      (cond
        (zero? i) (list j w)
        (zero? j) (list i v)
        :else (list 1 (semigroup (list v w)))))
    (list 0 0)))

; Get the dual of a monoid
(defmethod dual :locus.set.copresheaf.structure.core.protocols/monoid
  [semigroup]

  (Monoid.
    (underlying-set semigroup)
    (fn [arg]
      (semigroup (reverse arg)))
    (identity-element semigroup)))

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







