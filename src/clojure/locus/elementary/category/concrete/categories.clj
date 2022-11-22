(ns locus.elementary.category.concrete.categories
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.object :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all])
  (:import (locus.elementary.category.concrete.object ConcreteCategory)))

; The category of partial functions is a concrete category
(defn nullable-set
  [coll]

  (conj
    (set
      (map
        (fn [i]
          #{i})
        coll))
    #{}))

(defn nullable-function
  [func]

  (->SetFunction
    (nullable-set (inputs func))
    (nullable-set (outputs func))
    (fn [coll]
      (set (map func coll)))))

(def partial-sets
  (ConcreteCategory.
    (->UnitalQuiver
      partial-function?
      universal?
      source-object
      target-object
      partial-identity-function)
    (fn [[a b]]
      (compose a b))
    (fn [obj]
      (nullable-set obj))
    (fn [arrow]
      (nullable-function arrow))))

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

; Categories of single object categories and thin categories
(def set-monoids
  (ConcreteCategory.
    (as-unital-quiver
      monoid?
      monoid-homomorphism?)
    (fn [[a b]]
      (compose a b))
    underlying-set
    underlying-function))

(def set-groups
  (ConcreteCategory.
    (as-unital-quiver
      group?
      group-homomorphism?)
    (fn [[a b]]
      (compose a b))
    underlying-set
    underlying-function))

(def set-preorders
  (ConcreteCategory.
    (as-unital-quiver
      thin-category?
      monotone-map?)
    (fn [[a b]]
      (compose a b))
    underlying-set
    underlying-function))

(def set-partial-orders
  (ConcreteCategory.
    (as-unital-quiver
      skeletal-thin-category?
      monotone-map?)
    (fn [[a b]]
      (compose a b))
    underlying-set
    underlying-function))

; The concrete category of categories
(def cat
  (ConcreteCategory
    (as-unital-quiver
      category?
      functor?)
    (fn [[a b]]
      (compose a b))
    (fn [obj]
      (categorical-elements obj))
    (fn [arrow]
      (categorical-elements-function arrow))))