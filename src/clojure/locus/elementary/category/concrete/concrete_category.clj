(ns locus.elementary.category.concrete.concrete-category
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.transformation.transformation-monoid :refer :all]
            [locus.elementary.group.permutation.permutation-group :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all])
  (:import (locus.elementary.semigroup.transformation.transformation_monoid TransformationMonoid)
           (locus.elementary.group.permutation.permutation_group PermutationGroup)))

; A concrete category is simply a special type of category with an
; underlying copresheaf of sets and functions. It is an important part of
; the topos theory of copresheaves, because it is another way of handling
; the data of a copresheaf associated to a category.

(deftype ConcreteCategory [quiver op object-function morphism-function]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] (underlying-quiver quiver))
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (identity-morphism-of quiver obj))
  (underlying-unital-quiver [this] quiver)

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ConcreteCategoricalStructure
  (object-to-set [this object]
    (object-function object))
  (morphism-to-function [this morphism]
    (morphism-function morphism)))

(derive ConcreteCategory :locus.elementary.copresheaf.core.protocols/concrete-category)

; Extend a category with a faithful functor to the topos of sets
(defn extend-category
  [category object-function morphism-function]

  (->ConcreteCategory
    (underlying-unital-quiver category)
    category
    object-function
    morphism-function))

; Conversion routines for concrete categories
(defmulti to-concrete-category type)

(defmethod to-concrete-category TransformationMonoid
  [^TransformationMonoid monoid]

  (extend-category
    (to-category monoid)
    (fn [obj]
      (when (zero? obj)
        (.coll monoid)))
    (fn [morphism]
      (morphism-to-function monoid morphism))))

(defmethod to-concrete-category PermutationGroup
  [^PermutationGroup group]

  (extend-category
    (to-category group)
    (fn [obj]
      (when (zero? obj)
        (.coll group)))
    (fn [morphism]
      (morphism-to-function group morphism))))

; Restrict a concrete category
(defn restrict-concrete-category
  [^ConcreteCategory category, new-morphisms, new-objects]

  (ConcreteCategory.
    (unital-subquiver (underlying-unital-quiver category) new-morphisms new-objects)
    (.-op category)
    (.-object_function category)
    (.-morphism_function category)))

(defn wide-concrete-subcategory
  [^ConcreteCategory category, new-morphisms]

  (ConcreteCategory.
    (wide-unital-subquiver (underlying-unital-quiver category) new-morphisms)
    (.-op category)
    (.-object_function category)
    (.-morphism_function category)))

(defn full-concrete-subcategory
  [^ConcreteCategory category, new-objects]

  (ConcreteCategory.
    (full-unital-subquiver (underlying-unital-quiver category) new-objects)
    (.-op category)
    (.-object_function category)
    (.-morphism_function category)))

; The category of set relations is a concrete category
(def rel
  (ConcreteCategory.
    (->UnitalQuiver
      set-relation?
      universal?
      source-object
      target-object
      identity-relation)
    (fn [[a b]]
      (compose a b))
    (fn [obj]
      (->PowerSet obj))
    (fn [arrow]
      (to-function arrow))))

; By the same token we can consider the dual category of the topos of sets to be concrete
(def sets-opposite
  (ConcreteCategory.
    (->UnitalQuiver
      inverse-functional-set-relation?
      universal?
      source-object
      target-object
      identity-relation)
    (fn [[a b]]
      (compose a b))
    (fn [obj]
      (->PowerSet obj))
    (fn [arrow]
      (to-function arrow))))