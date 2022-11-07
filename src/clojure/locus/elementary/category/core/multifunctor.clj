(ns locus.elementary.category.core.multifunctor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]))

; A multifunctor is a functor F: C_1 x ... C_n -> D from a product of categories to some category
(deftype Multifunctor [source-categories target morphism-function object-function]
  AbstractMorphism
  (source-object [this]
    (apply category-product source-categories))
  (target-object [this]
    target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive Multifunctor :locus.elementary.copresheaf.core.protocols/functor)

; Underlying objects and morphisms of multifunctors
(defmethod get-object Multifunctor
  [multifunctor x]

  ((second-function multifunctor) x))

(defmethod get-morphism Multifunctor
  [multifunctor x]

  ((first-function multifunctor) x))

; Get the index components of a multifunctor
(defmethod index-multiplicands Multifunctor
  [^Multifunctor multifunctor]

  (.-source_categories multifunctor))

(defmethod index Multifunctor
  [^Multifunctor multifunctor]

  (source-object multifunctor))

; Convert multifunctors back to functors again
(defmethod to-functor Multifunctor
  [^Multifunctor multifunctor]

  (->Functor
    (source-object multifunctor)
    (target-object multifunctor)
    (partial get-object multifunctor)
    (partial get-morphism multifunctor)))

; Ontology of multifunctors
(defn multifunctor?
  [obj]

  (= (type obj) Multifunctor))