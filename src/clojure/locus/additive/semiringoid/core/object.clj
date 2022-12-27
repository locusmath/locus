(ns locus.additive.semiringoid.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]))

; A semiringoid is a CMon-enriched category, such as the category CMon of commutative monoids and
; monoid homomorphisms itself.

(deftype Semiringoid [quiver op hom]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] (underlying-quiver quiver))
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (identity-morphism-of quiver obj))
  (underlying-unital-quiver [this] quiver)

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Semiringoid :locus.additive.base.core.protocols/semiringoid)

; Underlying relations and multirelations of semiringoids
(defmethod underlying-multirelation Semiringoid
  [^Semiringoid semiringoid] (underlying-multirelation (underlying-quiver semiringoid)))

(defmethod underlying-relation Semiringoid
  [^Semiringoid semiringoid] (set (underlying-multirelation semiringoid)))

(defmethod visualize Semiringoid
  [^Semiringoid semiringoid] (visualize (underlying-quiver semiringoid)))

; Conversion routines for semiringoids
(defmulti to-semiringoid type)

(defmethod to-semiringoid Semiringoid
  [^Semiringoid semiringoid] semiringoid)

; Ontology of semiringoids
(defmethod semiringoid? Semiringoid
  [semiringoid] true)

