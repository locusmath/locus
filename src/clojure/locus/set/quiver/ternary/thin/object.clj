(ns locus.set.quiver.ternary.thin.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.ternary.core.object :refer :all]))

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

(derive ThinTernaryQuiver :locus.set.quiver.structure.core.protocols/thin-ternary-quiver)

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