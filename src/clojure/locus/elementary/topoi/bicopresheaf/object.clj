(ns locus.elementary.topoi.bicopresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.concrete.concrete-category :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.algebra.category.core.bifunctor :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.topoi.copresheaf.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.topoi.copresheaf.morphism MorphismOfCopresheaves)))

; Bicopresheaves are bifunctors to the topos of sets. A bicopresheaf has two different
; index categories C and D. It can be treated as a presheaf itself by using the product
; category C^D, and the topos Sets^{C x D} so bicopresheaves are still part of our fundamental
; topos theory of presheaves. Finally, bicopresheaves can be treated as a special type of
; structure copresheaf by the functor f : Sets^D -> Sets which makes a presheaf topos
; into a concrete category.

(deftype Bicopresheaf [first-source second-source object-function morphism-function]
  AbstractMorphism
  (source-object [this] (category-product first-source second-source))
  (target-object [this] sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive Bicopresheaf :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Index categories of bicopresheaves
(defmethod index Bicopresheaf
  [^Bicopresheaf bicopresheaf] (source-object bicopresheaf))

(defmethod index-multiplicands Bicopresheaf
  [^Bicopresheaf bicopresheaf]

  (list
    (.-first_source bicopresheaf)
    (.-second_source bicopresheaf)))

; Get the sets and functions of a bicopresheaf
(defmethod get-set Bicopresheaf
  [bicopresheaf x]

  (object-apply bicopresheaf x))

(defmethod get-function Bicopresheaf
  [bicopresheaf x]

  (morphism-apply bicopresheaf x))

; Get the objects and morphisms of a bicopresheaf
(defmethod get-object Bicopresheaf
  [bicopresheaf x]

  (get-set bicopresheaf x))

(defmethod get-morphism Bicopresheaf
  [bicopresheaf x]

  (get-function bicopresheaf x))

; Get a copresheaf by partial application of a bicopresheaf
(defn get-copresheaf
  [^Bicopresheaf bicopresheaf, x]

  (let [x-identity (identity-morphism-of (.-first_source bicopresheaf) x)]
    (->Copresheaf
      (.-second_source bicopresheaf)
      (fn [obj]
        (get-set bicopresheaf (list x obj)))
      (fn [arrow]
        (get-function bicopresheaf (list x-identity arrow))))))

(defn get-dual-copresheaf
  [^Bicopresheaf bicopresheaf, y]

  (let [y-identity (identity-morphism-of (.-second_source bicopresheaf) y)]
    (->Copresheaf
      (.-first_source bicopresheaf)
      (fn [obj]
        (get-set bicopresheaf (list obj y)))
      (fn [arrow]
        (get-function bicopresheaf (list arrow y-identity))))))

; Convert bicopresheaves into functors
(defmethod to-functor Bicopresheaf
  [^Bicopresheaf bicopresheaf]

  (->Functor
    (source-object bicopresheaf)
    (target-object bicopresheaf)
    (first-function bicopresheaf)
    (second-function bicopresheaf)))

; Generalized conversion routines for bicopresheaves
(defmulti to-bicopresheaf type)

(defmethod to-bicopresheaf Bicopresheaf
  [bicopresheaf] bicopresheaf)

(defmethod to-bicopresheaf Copresheaf
  [copresheaf]

  (->Bicopresheaf
    (thin-category (weak-order [#{0}]))
    (index copresheaf)
    (constantly copresheaf)
    (constantly (identity-morphism copresheaf))))

(defmethod to-bicopresheaf MorphismOfCopresheaves
  [morphism]

  (->Bicopresheaf
    (thin-category (weak-order [#{0} #{1}]))
    (index (source-object morphism))
    (fn [i]
      (case i
        0 (source-object morphism)
        1 (target-object morphism)))
    (fn [[i j]]
      (case [i j]
        [0 0] (identity-morphism (source-object morphism))
        [0 1] morphism
        [1 1] (identity-morphism (target-object morphism))))))

; Dual bicopresheaves
(defn dual-bicopresheaf
  [^Bicopresheaf bicopresheaf]

  (->Bicopresheaf
    (.-second_source bicopresheaf)
    (.-first_source bicopresheaf)
    (.-object_function bicopresheaf)
    (comp (.-morphism_function bicopresheaf) reverse)))

; The dual concept of a morphism of copresheaves is a copresheaf of functions which can  be defined
; by a functor from a category to the fundamental topos Sets^(->)
(defn copresheaf-of-functions
  [morphism]

  (->Bicopresheaf
    (index (source-object morphism))
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (to-copresheaf (morphism-of-copresheaves-component-function morphism obj)))
    (fn [arrow]
      (to-morphism-of-copresheaves (morphism-of-copresheaves-component-diamond morphism arrow)))))

; Componentwise addition of copresheaves
(defn componentwise-add-copresheaves
  [& bicopresheaves]

  (Bicopresheaf.
    (.-first_source (first bicopresheaves))
    (.-second_source (first bicopresheaves))
    (fn [obj]
      (apply
        index-sum
        (map
          (fn [bicopresheaf]
            (get-object bicopresheaf obj))
          bicopresheaves)))
    (fn [arrow]
      (apply
        morphism-index-sum
        (map
          (fn [bicopresheaf]
            (get-morphism bicopresheaf arrow))
          bicopresheaves)))))

; Ontology of bicopresheaves
(defn bicopresheaf?
  [obj]

  (= (type obj) Bicopresheaf))