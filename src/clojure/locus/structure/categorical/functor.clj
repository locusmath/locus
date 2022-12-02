(ns locus.structure.categorical.functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.category.concrete.categories :refer :all]
            [locus.structure.preposetal.functor :refer :all]
            [locus.structure.monoidal.functor :refer :all])
  (:import (locus.structure.monoidal.functor MonoidalFunctor)
           (locus.structure.preposetal.functor PreposetalFunctor)
           (locus.elementary.topoi.copresheaf.object Copresheaf)))

; A presheaf of categories is a functor F: C -> Cat, which means that it is a functor valued in categories.
; It is a presheaf in the sense that Cat is a concrete category whose elements are structured sets consisting
; of objects and morphisms. Thusly, we can consider categorical functors to be special types of structure
; presheaves.

(deftype CategoricalFunctor [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] cat)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive CategoricalFunctor :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Get objects and morphisms associated to category valued functors
(defmethod get-object CategoricalFunctor
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism CategoricalFunctor
  [functor x]

  ((first-function functor) x))

; As structure copresheaves every single category value functor has an underlying copresheaf
(defmethod get-set CategoricalFunctor
  [functor x]

  (categorical-elements (get-object functor x)))

(defmethod get-function CategoricalFunctor
  [functor x]

  (categorical-elements-function (get-morphism functor x)))

; Every category valued functor has some source index category
(defmethod index CategoricalFunctor
  [^CategoricalFunctor functor]

  (.-category functor))

; Conversion routines to be applied to category valued functors
(defmethod to-functor CategoricalFunctor
  [functor]

  (->Functor
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

(defmethod to-copresheaf CategoricalFunctor
  [functor]

  (->Copresheaf
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Conversion routines to convert things into category valued functors
(defmulti to-categorical-functor type)

(defmethod to-categorical-functor :locus.elementary.copresheaf.core.protocols/category
  [category]

  (->CategoricalFunctor
    (thin-category (weak-order [#{0}]))
    (constantly category)
    (constantly (identity-morphism category))))

(defmethod to-categorical-functor :locus.elementary.copresheaf.core.protocols/functor
  [functor]

  (->CategoricalFunctor
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object functor)
        1 (target-object functor)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism (source-object functor))
        [1 1] (identity-morphism (target-object functor))
        [0 1] functor))))

(defmethod to-categorical-functor MonoidalFunctor
  [^MonoidalFunctor functor]

  (->CategoricalFunctor
    (.-index functor)
    (.-object_function functor)
    (.-morphism_function functor)))

(defmethod to-categorical-functor PreposetalFunctor
  [^PreposetalFunctor functor]

  (->CategoricalFunctor
    (.-index functor)
    (.-object_function functor)
    (.-morphism_function functor)))

(defmethod to-categorical-functor Copresheaf
  [copresheaf]

  (->CategoricalFunctor
    (index copresheaf)
    (fn [obj]
      (discrete-category (get-set copresheaf obj)))
    (fn [arrow]
      (discrete-functor (get-function copresheaf arrow)))))

; Ontology of category valued functors
(defn categorical-functor?
  [functor]

  (= (type functor) CategoricalFunctor))