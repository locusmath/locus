(ns locus.algebra.category.core.bifunctor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; A bifunctor is any functor F : C x D -> E.
(deftype Bifunctor [first-source second-source target morphism-function object-function]
  AbstractMorphism
  (source-object [this]
    (category-product first-source second-source))
  (target-object [this]
    target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive Bifunctor :locus.elementary.copresheaf.core.protocols/functor)

; Bifunctors can be treated like functors, so they have underlying objects and morphisms
(defmethod get-object Bifunctor
  [bifunctor x]

  ((second-function bifunctor) x))

(defmethod get-morphism Bifunctor
  [bifunctor x]

  ((first-function bifunctor) x))

; Index categories of a bifunctor and their components
(defmethod index-multiplicands Bifunctor
  [^Bifunctor bifunctor]

  (list (.-first_source bifunctor) (.-second_source bifunctor)))

(defmethod index Bifunctor
  [^Bifunctor bifunctor]

  (category-product (.-first_source bifunctor) (.-second_source bifunctor)))

; To get the dual of a bifunctor just switch the order of its index categories
(defn dual-bifunctor
  [^Bifunctor bifunctor]

  (->Bifunctor
    (.-second_source bifunctor)
    (.-first_source bifunctor)
    (.-target bifunctor)
    (comp (.-morphism_function bifunctor) reverse)
    (.-object_function bifunctor)))

; Treat a bifunctor as a functor-valued functor
(defn get-functor
  [bifunctor x]

  (let [x-identity (identity-morphism-of (.-first_source bifunctor) x)]
    (->Functor
     (.-second_source bifunctor)
     (.-target bifunctor)
     (fn [obj]
       (get-object bifunctor (list x obj)))
     (fn [arrow]
       (get-morphism bifunctor (list x-identity arrow))))))

(defn get-dual-functor
  [bifunctor y]

  (let [y-identity (identity-morphism-of (.-second_source bifunctor) y)]
    (->Functor
      (.-first_source bifunctor)
      (.-target bifunctor)
      (fn [obj]
        (get-object bifunctor (list obj y)))
      (fn [arrow]
        (get-morphism bifunctor (list arrow y-identity))))))

; Convert a bifunctor into an ordinary functor by taking products
(defmethod to-functor Bifunctor
  [^Bifunctor bifunctor]

  (->Functor
    (source-object bifunctor)
    (target-object bifunctor)
    (partial get-object bifunctor)
    (partial get-morphism bifunctor)))

; Ontology of bifunctors
(defn bifunctor?
  [obj]

  (= (type obj) Bifunctor))
