(ns locus.set.quiver.ternary.thin.morphism
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
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.quiver.ternary.core.object :refer :all]
            [locus.set.quiver.ternary.core.morphism :refer :all]
            [locus.set.quiver.ternary.thin.object :refer :all])
  (:import (locus.set.quiver.ternary.thin.object ThinTernaryQuiver)))

; Morphisms of thin ternary quivers are simply homomorphisms of ternary relations
(deftype MorphismOfThinTernaryQuivers [source-quiver target-quiver func]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] (partial map func))
  (second-function [this] func))

(derive MorphismOfThinTernaryQuivers :locus.set.quiver.structure.core.protocols/morphism-of-ternary-quivers)

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