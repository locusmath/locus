(ns locus.ordered.category.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.commutative.monoid.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.ordered.monoid.object :refer :all])
  (:import (locus.ordered.monoid.object PreorderedMonoid)))

; A preordered category is a category enriched over the cartesian monoidal category of preorders,
; which is itself a subcategory of the category of categories. This makes preordered categories
; into the most basic examples of 2-categories.

(deftype PreorderedCategory [quiver op hom order]
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
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PreorderedCategory :locus.set.copresheaf.structure.core.protocols/category)

; Underlying relations for preordered categories
(defmethod underlying-multirelation PreorderedCategory
  [^PreorderedCategory category] (underlying-multirelation (underlying-quiver category)))

(defmethod underlying-relation PreorderedCategory
  [^PreorderedCategory category] (underlying-relation (underlying-quiver category)))

(defmethod underlying-preorder PreorderedCategory
  [^PreorderedCategory category] (.-order category))

(defmethod visualize PreorderedCategory
  [^PreorderedCategory category] (visualize (underlying-quiver category)))

; General conversion routines for preordered categories
(defmulti to-preordered-category type)

(defmethod to-preordered-category PreorderedCategory
  [^PreorderedCategory category] category)

(defmethod to-preordered-category PreorderedMonoid
  [^PreorderedMonoid monoid]

  (->PreorderedCategory
    (underlying-quiver monoid)
    (fn [[a b]]
      (monoid (list a b)))
    (constantly (underlying-preorder monoid))
    (underlying-preorder monoid)))

; Convert a preordered category back into an elementary category
(defmethod to-category PreorderedCategory
  [^PreorderedCategory category]

  (->Category (.-quiver category) (.-op category)))

; Constructors for special types of preordered categories
(defn discrete-category
  [category]

  (->PreorderedCategory
    (underlying-quiver category)
    (fn [[a b]]
      (category (list a b)))
    (fn [[a b]]
      (discrete-preorder (quiver-hom-class category a b)))
    (discrete-preorder (objects category))))

(defn indiscrete-category
  [category]

  (->PreorderedCategory
    (underlying-quiver category)
    (fn [[a b]]
      (category (list a b)))
    (fn [[a b]]
      (complete-preposet (quiver-hom-class category a b)))
    (complete-preposet (objects category))))

; The category of preorders is enriched in itself
(def preorders
  (->PreorderedCategory
    (as-unital-quiver
      thin-category?
      monotone-map?)
    (fn [[a b]]
      (compose a b))
    (fn [[a b]]
      (hom-preorder-of-monotone-maps a b))
    (->Poset
      monotone-map?
      (fn [[a b]]
       (submorphism? a b)))))

; Ontology of preordered categories
(defn preordered-category?
  [category]

  (= (type category) PreorderedCategory))

(defn ordered-category?
  [category]

  (and
    (preordered-category? category)
    (skeletal-thin-category? (underlying-preorder category))))
