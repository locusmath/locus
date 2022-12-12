(ns locus.set.tree.compoid.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.quiver.ternary.core.object :refer :all]
            [locus.set.tree.two-quiver.core.object :refer :all]
            [locus.set.tree.two-quiver.path.object :refer :all]
            [locus.set.tree.compoid.core.object :refer :all]))

; The topos of compositional quivers is a natural generalisation of the category of categories.
; Therefore, the morphisms of composition quivers are like functors, and we implement special
; mechanisms for converting functors and their generalisations into morphisms of composition
; quivers. There also special means of treating morphisms of composition quivers as if
; they are themselves functors.
(deftype MorphismOfCompoids [source target path-function morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MorphismOfCompoids :locus.set.logic.structure.protocols/morphism-of-copresheaves)

; Composition and identities in the topos of composition quivers
(defmethod identity-morphism Compoid
  [quiver]

  (->MorphismOfCompoids
    quiver
    quiver
    identity
    identity
    identity))

(defmethod compose* MorphismOfCompoids
  [^MorphismOfCompoids a, ^MorphismOfCompoids b]

  (->MorphismOfCompoids
    (source-object b)
    (target-object b)
    (comp (.-path_function a) (.-path_function b))
    (comp (.-morphism_function a) (.-morphism_function b))
    (comp (.-object_function a) (.-object_function b))))

; Multi method for converting objects into morphisms of composition quivers
(defmulti to-morphism-of-composition-quivers type)

(defmethod to-morphism-of-composition-quivers MorphismOfCompoids
  [morphism] morphism)

; Ontology of morphisms of composition quivers
(defn morphism-of-composition-quivers?
  [morphism]

  (= (type morphism) MorphismOfCompoids))