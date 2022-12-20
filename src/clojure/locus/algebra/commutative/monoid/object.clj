(ns locus.algebra.commutative.monoid.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.con.core.setpart :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all])
  (:import (locus.algebra.commutative.semigroup.object CommutativeSemigroup)))

; Commutative monoids are the same thing as N-semimodules. Once you have loaded the preliminary
; libraries, then you can convert a commutative monoid into an N-semimodule using the
; to-semimodule method. The difference between commutative semigroups and commutative monoids,
; means that this is not possible for commutative semigroups. To resolve this, we provide the
; adjoin-identity method which takes a commutative semigroup and produces a commutative
; monoid from it.

(deftype CommutativeMonoid [elems rel op id]
  ConcreteObject
  (underlying-set [this] elems)

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

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive CommutativeMonoid :locus.set.copresheaf.structure.core.protocols/commutative-monoid)

; Conversion routines for commutative monoids
(defmulti to-commutative-monoid type)

(defmethod to-commutative-monoid CommutativeMonoid
  [commutative-monoid] commutative-monoid)

(defmethod to-commutative-monoid CommutativeSemigroup
  [^CommutativeSemigroup commutative-semigroup]

  (let [identities (identity-elements commutative-semigroup)]
    (when (not (empty? identities))
      (->CommutativeMonoid
        (.-elems commutative-semigroup)
        (.-rel commutative-semigroup)
        (.-op commutative-semigroup)
        (first identities)))))

; Identity elements of commutative monoids
(defmethod identity-elements CommutativeMonoid
  [^CommutativeMonoid monoid]

  #{(.id monoid)})

; The natural preorder of a commutative monoid
(defmethod natural-preorder CommutativeMonoid
  [^CommutativeMonoid monoid]

  (.-rel monoid))

; Duals of commutative monoids
(defmethod dual CommutativeMonoid
  [^CommutativeMonoid commutative-monoid] commutative-monoid)

(defmethod product :locus.set.copresheaf.structure.core.protocols/monoid
  [& monoids]

  (CommutativeMonoid.
    (apply cartesian-product (map underlying-set monoids))
    (apply product-relation (map natural-preorder monoids))
    (apply semigroup-product-function monoids)
    (map identity-element monoids)))

; Adjoin identities to commutative semigroups
(defmethod adjoin-identity CommutativeSemigroup
  [commutative-semigroup]

  (let [new-collection (cartesian-coproduct #{0} (underlying-set commutative-semigroup))
        identity-element (list 0 0)
        rel (natural-preorder commutative-semigroup)]
    (->CommutativeMonoid
      new-collection
      (fn [[[i v] [j w]]]
        (cond
          (zero? i) true
          (zero? j) false
          :else (rel (list v w))))
      (fn [[[i v] [j w]]]
        (cond
          (zero? i) (list j w)
          (zero? j) (list i v)
          :else (list 1 (commutative-semigroup (list v w)))))
      identity-element)))