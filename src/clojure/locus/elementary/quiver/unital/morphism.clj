(ns locus.elementary.quiver.unital.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all])
  (:import [locus.elementary.quiver.core.object Quiver]
           [locus.base.function.core.object SetFunction]
           (locus.elementary.quiver.unital.object UnitalQuiver)))

; The topos of unital quivers is constructed as a presheaf category over the index category
; of unital quivers, which is a category with two objects and seven morphisms: the
; source morphism, the target morphism, the identity morphism, the source identity,
; and the target identity morphisms with the obvious compositions. Then the morphisms in
; this category are the natural transformations of corresponding presheaves. A useful
; instance of morphisms of unital quivers comes from the data of a functor of categories, then
; the morphism of unital quivers describe the fact that the functor preserves identities.

; Generalized morphisms of in the topos of unital quivers
(defprotocol StructuredMorphismOfUnitalQuivers
  "A structured morphism of unital quivers, such as a functor, is any morphism equipped with a
   functor to the topos of unital quivers."

  (underlying-morphism-of-unital-quivers [this]
    "Get the underlying morphism of unital quivers of a morphism."))

; Morphisms in the topos of unital quivers
(deftype MorphismOfUnitalQuivers [source-quiver target-quiver input-function output-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      source-quiver
      target-quiver
      input-function
      output-function))

  StructuredMorphismOfUnitalQuivers
  (underlying-morphism-of-unital-quivers [this] this))

(derive MorphismOfUnitalQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-unital-quivers)

; Get the morphisms of identity element functions of a morphism of unital quivers
; the order of the functions in the morphism is transposed because the identity
; element function goes backwards between vertices and edges.
(defn morphism-of-identity-element-functions
  [morphism]

  (->Diamond
    (identity-element-function (source-object morphism))
    (identity-element-function (target-object morphism))
    (second-function morphism)
    (first-function morphism)))

(defn morphism-of-source-identity-functions
  [morphism]

  (->Diamond
    (source-identity-function (source-object morphism))
    (source-identity-function (target-object morphism))
    (first-function morphism)
    (first-function morphism)))

(defn morphism-of-target-identity-functions
  [morphism]

  (->Diamond
    (target-identity-function (source-object morphism))
    (target-identity-function (target-object morphism))
    (first-function morphism)
    (first-function morphism)))

; Composition and identities in the topos of unital quivers
(defmethod compose* MorphismOfUnitalQuivers
  [a b]

  (MorphismOfUnitalQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (first-function a) (first-function b))
    (compose-functions (second-function a) (second-function b))))

(defmethod identity-morphism UnitalQuiver
  [quiv]

  (MorphismOfUnitalQuivers.
    quiv
    quiv
    (identity-function (first-set quiv))
    (identity-function (second-set quiv))))

; Products and coproducts in the topos of morphisms of unital quivers
(defmethod product MorphismOfUnitalQuivers
  [& args]

  (->MorphismOfUnitalQuivers
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map first-function args))
    (apply product (map second-function args))))

(defmethod coproduct MorphismOfUnitalQuivers
  [& args]

  (->MorphismOfUnitalQuivers
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map first-function args))
    (apply coproduct (map second-function args))))

; Ontology of morphisms in the topos of unital quivers
(defn morphism-of-unital-quivers?
  [morphism]

  (= (type morphism) MorphismOfUnitalQuivers))