(ns locus.additive.ringoid.core.object
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
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.abelian.group.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]))

; A ringoid is an Ab-enriched category. This is the horizontal categorification of the abstract
; algebraic concept of a ring.

(deftype Ringoid [quiver op hom]
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

(derive Ringoid :locus.additive.base.core.protocols/ringoid)

; Underlying multirelations of ringoids as categories
(defmethod underlying-multirelation Ringoid
  [^Ringoid ringoid] (underlying-multirelation (underlying-quiver ringoid)))

(defmethod underlying-relation Ringoid
  [^Ringoid ringoid] (set (underlying-multirelation  ringoid)))

(defmethod visualize Ringoid
  [^Ringoid ringoid] (visualize (underlying-quiver ringoid)))

; Ontology of ringoids
(defmethod ringoid? Ringoid
  [^Ringoid ringoid] true)
