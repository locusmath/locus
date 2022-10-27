(ns locus.structure.bicopresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.topoi.copresheaf.morphism :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.topoi.copresheaf.morphism MorphismOfCopresheaves)))

; Bicopresheaves are functors from a category C into a copresheaf topos Sets^D. So when written
; out they appear as functors of the form F: C -> Sets^D. A bicopresheaf has two different
; index categories C and D. It can be treated as a presheaf itself by using the product
; category C^D, and the topos Sets^{C x D} so bicopresheaves are still part of our fundamental
; topos theory of presheaves. Finally, bicopresheaves can be treated as a special type of
; structure copresheaf by the functor f : Sets^D -> Sets which makes a presheaf topos
; into a concrete category.

(deftype Bicopresheaf [source-index target-index object-function morphism-function]
  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive Bicopresheaf :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; As structure copresheaves every bicopresheaf has an underlying index category
(defmethod index Bicopresheaf
  [^Bicopresheaf bicopresheaf]

  (.-source_index bicopresheaf))

(defn target-index
  [^Bicopresheaf bicopresheaf]

  (.-target_index bicopresheaf))

; Bicopresheaves are structure copresheaves, so they have underlying objects and morphisms
(defmethod get-object Bicopresheaf
  [bicopresheaf object]

  ((second-function bicopresheaf) object))

(defmethod get-morphism Bicopresheaf
  [bicopresheaf morphism]

  ((first-function bicopresheaf) morphism))

; Bicopresheaves are structure copresheaves. It follows that they have underlying copresheaves.
(defmethod get-set Bicopresheaf
  [bicopresheaf object]

  (sections (get-object bicopresheaf object)))

(defmethod get-function Bicopresheaf
  [bicopresheaf morphism]

  (section-function (get-morphism bicopresheaf morphism)))

; Bicopresheaves are both structure copresheaves and bifunctorial presheaves. The deeper concept
; can be acquired by using the get set in and get function in methods.
(defn get-set-in
  [bicopresheaf x y]

  (get-set (get-object bicopresheaf x) y))

(defn get-function-in
  [bicopresheaf x y]

  (get-function (get-morphism bicopresheaf x) y))

; As structure copresheaves, bicopresheaves have underlying copresheaves
(defmethod to-copresheaf Bicopresheaf
  [bicopresheaf]

  (Copresheaf.
    (index bicopresheaf)
    (partial get-set bicopresheaf)
    (partial get-function bicopresheaf)))

; As presheaves of presheaves, bicopresheaves also have a deeper underlying presheaf
(defn deep-index
  [bicopresheaf]

  (category-product
    (index bicopresheaf)
    (target-index bicopresheaf)))

(defn deep-copresheaf
  [bicopresheaf]

  (->Copresheaf
    (deep-index bicopresheaf)
    (fn [[a b]]
      (get-set-in bicopresheaf a b))
    (fn [[a b]]
      (get-function-in bicopresheaf a b))))

; As a bifunctor a bicopresheaf has a dual defined by switching index categories
(defn get-dual-object
  [copresheaf d]

  (->Copresheaf
    (target-index copresheaf)
    (fn [c-object]
      (get-set-in copresheaf c-object d))
    (fn [c-arrow]
      (morphism-of-copresheaves-component-function
        (get-morphism copresheaf c-arrow)
        d))))

(defn get-dual-morphism
  [copresheaf d-arrow]

  (let [cat (target-index copresheaf)
        source (source-element cat d-arrow)
        target (target-element cat d-arrow)]
    (->MorphismOfCopresheaves
      (get-dual-object copresheaf source)
      (get-dual-object copresheaf target)
      (fn [c-object]
        (get-function-in copresheaf c-object d-arrow)))))

(defn dual-bicopresheaf
  [bicopresheaf]

  (->Bicopresheaf
    (target-index bicopresheaf)
    (index bicopresheaf)
    (partial get-dual-object bicopresheaf)
    (partial get-dual-morphism bicopresheaf)))

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
    (index (first bicopresheaves))
    (.-target_index (first bicopresheaves))
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