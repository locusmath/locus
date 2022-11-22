(ns locus.elementary.category.natural.transformation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all])
  (:import (locus.elementary.category.core.morphism Functor)))

; Let F,G be parallel functors C -> D. Then a natural transformation between them is a
; a function on the object set of C which produces elements of the morphism set of D.
; These natural transformations are then composed componentwise. Naturally transformations
; are particularly relevant as they include morphisms of copresheaves as a special case.
(deftype NaturalTransformation [source-functor target-functor func]
  AbstractMorphism
  (source-object [this] source-functor)
  (target-object [this] target-functor)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ::cone ::natural-transformation)
(derive ::cocone ::natural-transformation)
(derive NaturalTransformation ::natural-transformation)

; Natural transformations T: (F: C -> D) -> (G: C -> D) are functors U: T_2 x C -> D
(defmethod get-object ::natural-transformation
  [^NaturalTransformation transformation, [i v]]

  (case i
    0 (let [source-functor (source-object transformation)]
        (object-apply source-functor v))
    1 (let [target-functor (target-object transformation)]
        (object-apply target-functor v))))

(defmethod get-morphism ::natural-transformation
  [^NaturalTransformation transformation, [[i j] v]]

  (let [source-functor (source-object transformation)
        target-functor (target-object transformation)
        index-category (source-object source-functor)
        target-category (target-object source-functor)]
    (case [i j]
      [0 0] (morphism-apply source-functor v)
      [1 1] (morphism-apply target-functor v)
      [0 1] (target-category
              (list
                (morphism-apply target-functor v)
                (transformation (source-element index-category v)))))))

; Get the index categories of natural transformations treated as functors
(defn ordered-pair-product-category
  [category]

  (category-product
    (thin-category '#{(0 0) (0 1) (1 1)})
    category))

(defmethod index NaturalTransformation
  [^NaturalTransformation transformation]

  (ordered-pair-product-category (source-object (source-object transformation))))

; Composition and identities in functor categories
(defmethod identity-morphism Functor
  [functor]

  (let [target-category (target-object functor)]
    (NaturalTransformation.
      functor
      functor
      (fn [obj]
        (identity-morphism-of
          target-category
          (object-apply functor obj))))))

(defmethod compose* ::natural-transformation
  [a b]

  (NaturalTransformation.
    (source-object b)
    (target-object a)
    (fn [obj]
      (compose (a obj) (b obj)))))

; Get a morphism of constant functors
(defn morphism-of-constant-functors
  [source target target-morphism]

  (->NaturalTransformation
    (constant-functor source target (source-element target target-morphism))
    (constant-functor source target (target-element target target-morphism))
    (constantly target-morphism)))

; Natural transformations are functors over a product category
(defmethod to-functor NaturalTransformation
  [^NaturalTransformation transformation]

  (let [source-functor (source-object transformation)
        index-category (source-object source-functor)
        target-category (target-object source-functor)]
    (->Functor
      (index transformation)
      target-category
      (partial get-object transformation)
      (partial get-morphism transformation))))

; Conversion routines
(defmulti to-natural-transformation type)

(defmethod to-natural-transformation ::natural-transformation
  [func] func)

; Ontology of natural transformations
; These are the different classes of natural transformations that we make encounter in category theory.
(defmulti natural-transformation? type)

(defmethod natural-transformation? ::natural-transformation
  [func] true)

(defmethod natural-transformation? :default
  [func] false)

; Functor categories:
; Let C,D be categories and consider the hom class Hom(C,D) then all the functors from C
; to D are objects in a category whose morphisms are natural transformations. This method will
; create the resulting functor category.
(defn in-category-hom-class?
  [functor source-category target-category]

  (and
    (functor? functor)
    (= (source-object functor) source-category)
    (= (target-object functor) target-category)))

(defn functor-category
  [source-category target-category]

  (->Category
    (->UnitalQuiver
      (fn [morphism]
        (and
          (natural-transformation? morphism)
          (in-category-hom-class? (source-object morphism) source-category target-category)
          (in-category-hom-class? (target-object morphism) source-category target-category)))
      (fn [functor]
        (in-category-hom-class? functor source-category target-category))
      source-object
      target-object
      identity-morphism)
    (fn [[a b]]
      (compose a b))))
