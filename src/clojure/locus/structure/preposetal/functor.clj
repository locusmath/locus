(ns locus.structure.preposetal.functor
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.concrete.concrete-category :refer :all]
            [locus.algebra.category.concrete.categories :refer :all])
  (:import (locus.order.general.core.object Preposet)
           (locus.order.general.core.morphism MonotoneMap)))

; A preposetal functor is a functor from a category C to the category of preorders and monotone
; maps. It is a structure presheaf, as every preorder has an underlying set and every monotone
; map has an underlying function, so it is dealt with as part of our structure presheaf
; framework. As a structure presheaf, it is also a special type of category-valued functor.
; Using our structure copresheaf framework, every preposetal functor on a category C is
; associated to preshaef in the topos Sets^C. So presheaves of preorders can be related
; back to our fundamental presheaf theory.

(deftype PreposetalFunctor [index object-function morphism-function]
  AbstractMorphism
  (source-object [this] index)
  (target-object [this] set-preorders)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive PreposetalFunctor :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Preposetal functors are structure copresheaves which makes them types of functors
(defmethod get-object PreposetalFunctor
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism PreposetalFunctor
  [functor x]

  ((first-function functor) x))

; Preposetal functors are structure presheaves so they have underlying presheaves
(defmethod get-set PreposetalFunctor
  [functor x]

  (underlying-set (get-object functor x)))

(defmethod get-function PreposetalFunctor
  [functor x]

  (underlying-function (get-morphism functor x)))

; Every functor into the category of preorders must have a source category
(defmethod index PreposetalFunctor
  [^PreposetalFunctor functor] (.-index functor))

; Conversion routines to convert presheaves of preorders into other objects
(defmethod to-functor PreposetalFunctor
  [functor]

  (->Functor
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

(defmethod to-copresheaf PreposetalFunctor
  [functor]

  (->Copresheaf
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Conversion routines to take other objects and turn them into presheaves of preorders
(defmulti to-preposetal-functor type)

(defmethod to-preposetal-functor PreposetalFunctor
  [functor] functor)

(defmethod to-preposetal-functor Preposet
  [preorder]

  (->PreposetalFunctor
    (thin-category (weak-order [#{0}]))
    (constantly preorder)
    (constantly (identity-morphism preorder))))

(defmethod to-preposetal-functor MonotoneMap
  [morphism]

  (->PreposetalFunctor
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object morphism)
        1 (target-object morphism)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism (source-object morphism))
        [1 1] (identity-morphism (target-object morphism))
        [0 1] morphism))))

(defmethod to-preposetal-functor Copresheaf
  [copresheaf]

  (->PreposetalFunctor
    (index copresheaf)
    (fn [obj]
      (discrete-preorder (get-set copresheaf obj)))
    (fn [arrow]
      (discrete-monotone-map (get-function copresheaf arrow)))))

; Ontology of preposetal functors
(defn preposetal-functor?
  [functor]

  (= (type functor) PreposetalFunctor))

(defn chain-of-preposets?
  [functor]

  (and
    (preposetal-functor? functor)
    (total-order-category? (index functor))))

(defn preposet-object-functor?
  [functor]

  (and
    (preposetal-functor? functor)
    (let [cat (index functor)]
      (= (count (objects cat)) (count (morphisms cat)) 1))))

(defn preposet-morphism-functor?
  [functor]

  (and
    (preposetal-functor? functor)
    (let [cat (index functor)]
      (and
        (total-order-category? cat)
        (= (count (objects cat)) 2)))))

(defn preposet-isomorphism-functor?
  [functor]

  (and
    (preposetal-functor? functor)
    (let [cat (index functor)]
      (and
        (complete-thin-groupoid? cat)
        (= (count (objects cat)) 2)))))