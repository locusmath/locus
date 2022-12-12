(ns locus.set.tree.functional-quiver.core.morphism
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
            [locus.set.tree.structure.core.protocols :refer :all]
            [locus.set.tree.functional-quiver.core.object :refer :all])
  (:import (locus.set.quiver.binary.core.morphism MorphismOfQuivers)
           (locus.set.tree.functional_quiver.core.object FunctionalQuiver)))

; Morphisms in the topos of functional quivers
(deftype MorphismOfFunctionalQuivers [source target in-function morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MorphismOfFunctionalQuivers :locus.set.logic.structure.protocols/morphism-of-copresheaves)

; Composition and identities in the topos of functional quivers
(defmethod identity-morphism FunctionalQuiver
  [quiver]

  (->MorphismOfFunctionalQuivers quiver quiver identity identity identity))

(defmethod compose* MorphismOfFunctionalQuivers
  [a b]

  (->MorphismOfFunctionalQuivers
    (source-object b)
    (target-object a)
    (comp (.-in_function a) (.-in_function b))
    (comp (.-morphism_function a) (.-morphism_function b))
    (comp (.-object_function a) (.-object_function b))))

; Ontology of morphisms of functional quivers
(defn morphism-of-functional-quivers?
  [obj]

  (= (type obj) MorphismOfFunctionalQuivers))