(ns locus.set.copresheaf.quiver.dependency.thin-object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.mbr :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.copresheaf.quiver.unital.thin-object :refer :all]
            [locus.set.copresheaf.quiver.permutable.thin-object :refer :all]
            [locus.set.copresheaf.quiver.dependency.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

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

(derive ThinDependencyQuiver :locus.set.copresheaf.quiver.dependency.object/dependency-quiver)

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