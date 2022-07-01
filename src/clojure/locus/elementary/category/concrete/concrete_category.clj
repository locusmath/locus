(ns locus.elementary.category.concrete.concrete-category
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.transformation.transformation-monoid :refer :all]
            [locus.elementary.group.permutation.permutation-group :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all])
  (:import (locus.elementary.semigroup.transformation.transformation_monoid TransformationMonoid)
           (locus.elementary.group.permutation.permutation_group PermutationGroup)))

; A concrete category is simply a special type of category with an
; underlying copresheaf of sets and functions. It is an important part of
; the topos theory of copresheaves, because it is another way of handling
; the data of a copresheaf associated to a category.
(deftype ConcreteCategory [morphisms objects source target func id object-function morphism-function]
  ; Categories are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (id obj))
  (underlying-unital-quiver [this] (->UnitalQuiver morphisms objects source target id))

  ; Categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive ConcreteCategory :locus.elementary.function.core.protocols/concrete-category)

; Extend a category to make it into a concrete category
(defn extend-category
  [category object-function morphism-function]

  (ConcreteCategory.
    (morphisms category)
    (objects category)
    (source-fn category)
    (target-fn category)
    (.func category)
    (.id category)
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
    new-morphisms
    new-objects
    (.source category)
    (.target category)
    (.func category)
    (.id category)
    (.-object_function category)
    (.-morphism_function category)))


