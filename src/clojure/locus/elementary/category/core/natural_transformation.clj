(ns locus.elementary.category.core.natural-transformation
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.comma.morphism :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
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

(defn object-mapping
  [func] (.func func))

(defn morphism-mapping
  [natural-transformation]

  (fn [morphism]
    (->MorphismOfMorphisms
      ((first-function (source-object natural-transformation)) morphism)
      ((first-function (target-object natural-transformation)) morphism)
      (natural-transformation (source-object morphism))
      (natural-transformation (target-object morphism)))))

; Conversion routines
(defmulti to-natural-transformation type)

(defmethod to-natural-transformation :default
  [func] func)

; Composition and identities in categories of functors
(defmethod identity-morphism Functor
  [functor]

  (NaturalTransformation.
    functor
    functor
    (fn [obj]
      (identity-morphism
        ((second-function functor) obj)))))

(defmethod compose* NaturalTransformation
  [a b]

  (NaturalTransformation.
    (source-object b)
    (target-object a)
    (fn [obj]
      (compose (a obj) (b obj)))))

; Ontology of natural transformations
(defn natural-transformation?
  [func]

  (= (type func) NaturalTransformation))

(defn in-category-hom-class?
  [functor source-category target-category ]

  (and
    (functor? functor)
    (= (source-object functor) source-category)
    (= (target-object functor) target-category)))

; Functor categories:
; Let C,D be categories and consider the hom class Hom(C,D) then all the functors from C
; to D are objects in a category whose morphisms are natural transformations. This method will
; create the resulting functor category.
(defn functor-category
  [source-category target-category]

  (->Category
    (fn [morphism]
      (and
        (natural-transformation? morphism)
        (in-category-hom-class? (source-object morphism) source-category target-category)
        (in-category-hom-class? (target-object morphism) source-category target-category)))
    (fn [functor]
      (in-category-hom-class? functor source-category target-category))
    source-object
    target-object
    (fn [[a b]] (compose a b))
    identity-morphism))