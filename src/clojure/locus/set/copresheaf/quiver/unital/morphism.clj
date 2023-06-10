(ns locus.set.copresheaf.quiver.unital.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.quiver.binary.core.object Quiver]
           [locus.set.mapping.general.core.object SetFunction]
           (locus.set.copresheaf.quiver.unital.object UnitalQuiver)))

; The topos of unital quivers is constructed as a presheaf category over the index category
; of unital quivers, which is a category with two objects and seven morphisms: the
; source morphism, the target morphism, the identity morphism, the source identity,
; and the target identity morphisms with the obvious compositions. Then the morphisms in
; this category are the natural transformations of corresponding presheaves. A useful
; instance of morphisms of unital quivers comes from the data of a functor of categories, then
; the morphism of unital quivers describe the fact that the functor preserves identities.

; Morphisms in the topos of unital quivers
(deftype MorphismOfUnitalQuivers [source-quiver target-quiver input-function output-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] input-function)
  (second-function [this] output-function))

(derive MorphismOfUnitalQuivers :locus.set.copresheaf.structure.core.protocols/morphism-of-structured-unital-quivers)

; A structured morphism of unital quivers, such as a functor, is any morphism equipped with a
; forgetful functor to the topos of unital quivers. The underlying-morphism-of-unital-quivers
; get the result of applying this forgetful functor to such a morphism.
(defmulti underlying-morphism-of-unital-quivers type)

(defmethod underlying-morphism-of-unital-quivers MorphismOfUnitalQuivers
  [^MorphismOfUnitalQuivers morphism] morphism)

(defmethod underlying-morphism-of-unital-quivers :default
  [morphism]

  (->MorphismOfUnitalQuivers
    (underlying-unital-quiver (source-object morphism))
    (underlying-unital-quiver (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

; Components of morphisms of permutable quivers
(defmethod get-set MorphismOfUnitalQuivers
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function MorphismOfUnitalQuivers
  [morphism [[i j] v]]

  (let [source-data* [0 1 0 0 1 0 0]]
    (case [i j]
      [0 0] (get-function (source-object morphism) v)
      [1 1] (get-function (target-object morphism) v)
      [0 1] (compose
              (get-function (target-object morphism) v)
              (morphism-of-quivers-component-function morphism (get source-data* v))))))

; Get the morphisms of identity element functions of a morphism of unital quivers
; the order of the functions in the morphism is transposed because the identity
; element function goes backwards between vertices and edges.
(defn morphism-of-identity-element-functions
  [morphism]

  (->SetSquare
    (identity-element-function (source-object morphism))
    (identity-element-function (target-object morphism))
    (second-function morphism)
    (first-function morphism)))

(defn morphism-of-source-identity-functions
  [morphism]

  (->SetSquare
    (source-identity-function (source-object morphism))
    (source-identity-function (target-object morphism))
    (first-function morphism)
    (first-function morphism)))

(defn morphism-of-target-identity-functions
  [morphism]

  (->SetSquare
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