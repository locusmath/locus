(ns locus.elementary.nary-quiver.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]
            [locus.elementary.nary-quiver.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all])
  (:import (locus.elementary.nary_quiver.core.object NaryQuiver)))

; The topoi of nary quivers are the family of topoi of presheaves over the n arrow categories, which
; consist of two objects and up to n parallel edges going from the source set to the target set.
; The morphisms in this topoi are natural transformations of their corresponding copresheaves. As
; the index category has no more than two objects, these morphisms can be represented by
; a pair of two functions corresponding to the object and morphism sets of the two nary quivers.
(deftype MorphismOfNaryQuivers [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MorphismOfNaryQuivers :locus.elementary.copresheaf.core.protocols/structured-difunction)

; Identities and composition in topoi of nary quivers
(defmethod identity-morphism NaryQuiver
  [nary-quiver]

  (->MorphismOfNaryQuivers
    nary-quiver
    nary-quiver
    identity
    identity))

(defmethod compose* MorphismOfNaryQuivers
  [a b]

  (MorphismOfNaryQuivers.
    (source-object b)
    (target-object a)
    (comp (first-function a) (first-function b))
    (comp (second-function a) (second-function b))))

; Let f: Q1 -> Q2 be a morphism of nary quivers. Then each index of a component in the nary quiver
; there is a corresponding morphism of functions in the topos Sets^(->) which can be determined
; by an index reduction of the morphism of nary quivers as presented as a copresheaf.
(defn morphism-of-nth-component-functions
  [morphism i]

  (->Diamond
    (nth-component-function (source-object morphism) i)
    (nth-component-function (target-object morphism) i)
    (first-function morphism)
    (second-function morphism)))

; Ontology of morphisms of nary quivers
(defn morphism-of-nary-quivers?
  [morphism]

  (= (type morphism) MorphismOfNaryQuivers))