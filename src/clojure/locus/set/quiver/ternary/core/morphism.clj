(ns locus.set.quiver.ternary.core.morphism
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
            [locus.set.quiver.ternary.core.object :refer :all]))

; The topos of ternary quivers is the topos of presheaves over the index category T_{2,3} consisting
; of two objects with three parallel morphisms between them, all going in the same direction. It
; is denoted Sets^{T_{2,3}}. Its morphisms, on the other hand, are defined by a pair of functions
; one between the objects of a pair of ternary quivers and another between the morphisms. Such a
; morphism is then itself equivalent to an object in the presheaf topos Sets^{T_{2,3} x T_2}. So
; a number of topos theoretic operations like products and coproducts are also generalized
; to morphisms of ternary quivers.

(deftype MorphismOfTernaryQuivers [source-quiver target-quiver morphism-function object-function]
  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive MorphismOfTernaryQuivers :locus.set.quiver.structure.core.protocols/morphism-of-ternary-quivers)

; Component arrows of morphisms of ternary quivers
(defn morphism-of-ternary-quivers-component-function
  [morphism x]

  (case x
    0 (->SetFunction
        (first-set (source-object morphism))
        (first-set (target-object morphism))
        (first-function morphism))
    1 (->SetFunction
        (second-set (source-object morphism))
        (second-set (target-object morphism))
        (second-function morphism))))

; Components of morphisms of ternary quivers
(defmethod get-set MorphismOfTernaryQuivers
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function MorphismOfTernaryQuivers
  [morphism [[i j] v]]

  (let [source-data* [0 1 0 0 0]]
    (case [i j]
      [0 0] (get-function (source-object morphism) v)
      [1 1] (get-function (target-object morphism) v)
      [0 1] (compose
              (get-function (target-object morphism) v)
              (morphism-of-ternary-quivers-component-function morphism (get source-data* v))))))

; Get the morphism of first component functions from the ternary quiver morphism
(defn morphism-of-first-component-functions
  [^MorphismOfTernaryQuivers morphism]

  (->SetSquare
    (first-component-function (source-object morphism))
    (first-component-function (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

(defn morphism-of-second-component-functions
  [^MorphismOfTernaryQuivers morphism]

  (->SetSquare
    (second-component-function (source-object morphism))
    (second-component-function (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

(defn morphism-of-third-component-functions
  [^MorphismOfTernaryQuivers morphism]

  (->SetSquare
    (third-component-function (source-object morphism))
    (third-component-function (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

; Morphisms of quivers associated to a morphism of ternary quivers by forgetful functors
(defn morphism-of-front-quivers
  [^MorphismOfTernaryQuivers morphism]

  (->MorphismOfQuivers
    (front-quiver (source-object morphism))
    (front-quiver (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

(defn morphism-of-back-quivers
  [^MorphismOfTernaryQuivers morphism]

  (->MorphismOfQuivers
    (back-quiver (source-object morphism))
    (back-quiver (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

(defn morphism-of-outer-quivers
  [^MorphismOfTernaryQuivers morphism]

  (->MorphismOfQuivers
    (outer-quiver (source-object morphism))
    (outer-quiver (target-object morphism))
    (first-function morphism)
    (second-function morphism)))

; Composition and identities in the topos of ternary quivers
(defmethod identity-morphism :locus.set.quiver.structure.core.protocols/ternary-quiver
  [quiver]

  (->MorphismOfTernaryQuivers
    quiver
    quiver
    identity
    identity))

(defmethod compose* MorphismOfTernaryQuivers
  [a b]

  (MorphismOfTernaryQuivers.
    (source-object b)
    (target-object a)
    (comp (first-function a) (first-function b))
    (comp (second-function a) (second-function b))))

; Products and coproducts in the topos of morphisms of ternary quivers
(defmethod product MorphismOfTernaryQuivers
  [& morphisms]

  (->MorphismOfTernaryQuivers
    (apply product (map source-object morphisms))
    (apply product (map target-object morphisms))
    (apply product (map first-function morphisms))
    (apply product (map second-function morphisms))))

(defmethod coproduct MorphismOfTernaryQuivers
  [& morphisms]

  (->MorphismOfTernaryQuivers
    (apply coproduct (map source-object morphisms))
    (apply coproduct (map target-object morphisms))
    (apply coproduct (map first-function morphisms))
    (apply coproduct (map second-function morphisms))))

; Ontology of morphisms of ternary quivers
(defn morphism-of-ternary-quivers?
  [morphism]

  (= (type morphism) MorphismOfTernaryQuivers))
