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

; Thin objects in the topos of dependency quivers
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

; Products and coproducts in the topos of dependency quivers
(defmethod product ThinDependencyQuiver
  [& quivers]

  (ThinDependencyQuiver.
    (apply cartesian-product (map objects quivers))
    (apply product-relation (map morphisms quivers))))

(defmethod coproduct ThinDependencyQuiver
  [& quivers]

  (ThinDependencyQuiver.
    (apply cartesian-coproduct (map objects quivers))
    (apply sum-relation (map morphisms quivers))))

; Duals in the topos of dependency quivers
(defmethod dual ThinDependencyQuiver
  [^ThinDependencyQuiver quiver] quiver)