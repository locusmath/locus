(ns locus.quiver.ternary.thin.morphism
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
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.quiver.ternary.core.object :refer :all]
            [locus.quiver.ternary.core.morphism :refer :all]
            [locus.quiver.ternary.thin.object :refer :all])
  (:import (locus.quiver.ternary.thin.object ThinTernaryQuiver)))

; Morphisms of thin ternary quivers are simply homomorphisms of ternary relations
(deftype MorphismOfThinTernaryQuivers [source-quiver target-quiver func]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] (partial map func))
  (second-function [this] func))

(derive MorphismOfThinTernaryQuivers :locus.quiver.base.core.protocols/morphism-of-ternary-quivers)

; Composition and identities of thin ternary quivers
(defmethod identity-morphism ThinTernaryQuiver
  [^ThinTernaryQuiver quiver]

  (->MorphismOfThinTernaryQuivers quiver quiver identity))

(defmethod compose* MorphismOfThinTernaryQuivers
  [a b]

  (MorphismOfThinTernaryQuivers.
    (source-object b)
    (target-object a)
    (comp (.-func a) (.-func b))))