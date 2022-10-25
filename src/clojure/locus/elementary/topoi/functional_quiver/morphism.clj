(ns locus.elementary.topoi.functional-quiver.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.topoi.functional-quiver.object :refer :all])
  (:import (locus.elementary.quiver.core.morphism MorphismOfQuivers)
           (locus.elementary.topoi.functional_quiver.object FunctionalQuiver)))

; Morphisms in the topos of functional quivers
(deftype MorphismOfFunctionalQuivers [source target in-function morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers
    (MorphismOfQuivers. source target morphism-function object-function)))

; Composition and identities in the topos of functional quivers
(defmethod identity-morphism FunctionalQuiver
  [quiver]

  (->MorphismOfFunctionalQuivers
    quiver
    quiver
    identity
    identity
    identity))

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