(ns locus.elementary.composition-quiver.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.semigroupoid.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.semigroupoid.core.morphism :refer :all]
            [locus.elementary.composition-quiver.core.object :refer :all])
  (:import (locus.elementary.composition_quiver.core.object CompositionQuiver)
           (locus.elementary.category.core.morphism Functor)))

; The topos of compositional quivers is a natural generalisation of the category of categories.
; Therefore, the morphisms of composition quivers are like functors, and we implement special
; mechanisms for converting functors and their generalisations into morphisms of composition
; quivers. There also special means of treating morphisms of composition quivers as if
; they are themselves functors.

(deftype MorphismOfCompositionQuivers [source target path-function morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      (underlying-quiver source)
      (underlying-quiver target)
      (first-function this)
      (second-function this))))

(derive MorphismOfCompositionQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-quivers)

; Composition and identities in the topos of composition quivers
(defmethod identity-morphism CompositionQuiver
  [quiver]

  (->MorphismOfCompositionQuivers
    quiver
    quiver
    identity
    identity
    identity))

(defmethod compose* MorphismOfCompositionQuivers
  [^MorphismOfCompositionQuivers a, ^MorphismOfCompositionQuivers b]

  (->MorphismOfCompositionQuivers
    (source-object b)
    (target-object b)
    (comp (.-path_function a) (.-path_function b))
    (comp (.-morphism_function a) (.-morphism_function b))
    (comp (.-object_function a) (.-object_function b))))

; Multi method for converting objects into morphisms of composition quivers
(defmulti to-morphism-of-composition-quivers type)

(defmethod to-morphism-of-composition-quivers MorphismOfCompositionQuivers
  [morphism] morphism)

(defmethod to-morphism-of-composition-quivers :locus.elementary.copresheaf.core.protocols/partial-magmoid-homomorphism
  [functor]

  (let [morphism-function (first-function functor)
        object-function (second-function functor)]
    (->MorphismOfCompositionQuivers
     (to-compositional-quiver (source-object functor))
     (to-compositional-quiver (target-object functor))
     (fn [[a b]]
       (list (morphism-function a) (morphism-function b)))
     morphism-function
     object-function)))

; Ontology of morphisms of composition quivers
(defn morphism-of-composition-quivers?
  [morphism]

  (= (type morphism) MorphismOfCompositionQuivers))