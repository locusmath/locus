(ns locus.quiver.ternary.thin.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.ternary.core.object :refer :all]))

; Thin ternary quivers are essentially equivalent to ternary relations
(deftype ThinTernaryQuiver [edges vertices]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(first-set this) (second-set this)]))

  StructuredTernaryQuiver
  (first-component-fn [this] first)
  (second-component-fn [this] second)
  (third-component-fn [this]
    (fn [edge]
      (nth edge 2))))

(derive ThinTernaryQuiver :locus.quiver.base.core.protocols/thin-ternary-quiver)

; This is a special constructor for thin ternary quivers
(defn thin-ternary-quiver
  ([vertices edges]
   (ThinTernaryQuiver. vertices edges))
  ([edges]
   (ThinTernaryQuiver. (vertices edges) edges)))

; Thin ternary quivers have underlying relations
(defmethod underlying-multirelation ThinTernaryQuiver
  [^ThinTernaryQuiver quiver]

  (.-edges quiver))

(defmethod underlying-relation ThinTernaryQuiver
  [^ThinTernaryQuiver quiver]

  (.-edges quiver))