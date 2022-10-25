(ns locus.elementary.quiver.dependency.thin-object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.mbr :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.quiver.unital.thin-object :refer :all]
            [locus.elementary.quiver.permutable.thin-object :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]))

; A dependency quiver is said to be thin provided that for each hom class Hom(A,B) there is
; no more then one morphism in the class. In that case the dependency quiver is said to be
; thin and it can be described by a relation. The identity of an element is the equal
; ordered pair and the inverse of an ordered pair is its reversal.

(deftype ThinDependencyQuiver [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices)

  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] (->ThinQuiver vertices edges))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (->ThinUnitalQuiver vertices edges))
  (identity-morphism-of [this obj] (list obj obj))

  StructuredPermutableQuiver
  (underlying-permutable-quiver [this] (->ThinPermutableQuiver vertices edges))
  (invert-morphism [this morphism] (reverse morphism))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this] this))

(derive ThinDependencyQuiver :locus.elementary.quiver.dependency.object/dependency-quiver)

; Create a thin dependency quiver
(defn thin-dependency-quiver
  ([edges]
   (ThinDependencyQuiver. (vertices edges) edges))

  ([vertices edges]
   (ThinDependencyQuiver. vertices edges)))

; Underlying relations and multirelations for thin dependency quivers
(defmethod underlying-relation ThinDependencyQuiver
  [^ThinDependencyQuiver quiver] (.-edges quiver))

(defmethod underlying-multirelation ThinDependencyQuiver
  [^ThinDependencyQuiver quiver] (.-edges quiver))

(defmethod visualize ThinDependencyQuiver
  [^ThinDependencyQuiver quiver] (visualize (.-edges quiver)))

; Duals in the topos of dependency quivers
(defmethod dual ThinDependencyQuiver
  [^ThinDependencyQuiver quiver] quiver)