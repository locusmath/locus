(ns locus.elementary.category.morphism.category-morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.object.category-object :refer :all]
            [locus.elementary.semigroup.monoid.end :refer :all]
            [locus.elementary.group.core.aut :refer :all])
  (:import (locus.elementary.category.core.object Category)))

; We need to distinguish between source and target elements on the one
; hand and source and target objects on the other, by the fact that
; source and target objects are elements of the CategoryObject class.
(deftype CategoryMorphism [category morphism]
  AbstractMorphism
  (source-object [this]
    (CategoryObject. category (source-element category morphism)))
  (target-object [this]
    (CategoryObject. category (target-element category morphism))))

; Source and target object elements
(defn source-object-element
  [morphism]

  ((.source (.category morphism)) morphism))

(defn target-object-element
  [morphism]

  ((.target (.category morphism)) morphism))

; Composition and identities in arbitrary categories
(defmethod compose* CategoryMorphism
  [a b]

  (->CategoryMorphism
    (.category a)
    ((.func (.category a))
     (list (.morphism a) (.morphism b)))))

(defmethod identity-morphism CategoryObject
  [obj]

  (let [c (.category obj)]
    (CategoryMorphism.
      c
      ((.id ^Category c) (.object obj)))))

; Enumeration of automorphisms and endomorphisms
(defn category-morphisms
  [category]

  (set
    (map
      (fn [i]
        (CategoryMorphism. category i))
      (first-set category))))

(defn composable-morphisms?
  [a b]

  (= (target-object b)
     (source-object a)))

(defn morphism?
  [morphism]

  (= (type morphism) CategoryMorphism))

(defn endomorphism?
  [morphism]

  (= (source-object morphism)
     (target-object morphism)))

(defn identity-morphism?
  [morphism]

  (let [category (.category morphism)
        source (source-object morphism)
        target (target-object morphism)]
    (and
      (= source target)
      (= (.morphism morphism) ((.id ^Category category) source)))))

(defn inverses?
  [a b]

  (and
    (= (source-object a) (target-object b))
    (= (target-object a) (source-object b))
    (identity-morphism? (compose a b))
    (identity-morphism? (compose b a))))

(defn isomorphism?
  [morphism]

  (not
    (every?
      (fn [i]
        (not (inverses? morphism i)))
      (category-morphisms (.category morphism)))))

(def automorphism?
  (intersection
    endomorphism?
    isomorphism?))

; We need to be able to get the end monoid and the aut group of an
; object of a category, which can be achieved by morphism enumeration.
(defn enumerate-endomorphisms
  [ob]

  (set
    (filter
      (fn [i]
        (= (source-object-element i)
           (target-object-element i)
           (.object ob)))
      (category-morphisms (.category ob)))))

(defn enumerate-automorphisms
  [ob]

  (set
    (filter
      (fn [i]
        (and
          (isomorphism? i)
          (= (source-object-element i)
             (target-object-element i)
             (.object ob))))
      (category-morphisms (.category ob)))))

(defmethod end CategoryObject
  [obj]

  (->Monoid
    (enumerate-endomorphisms obj)
    (fn [[a b]]
      (compose a b))
    (identity-morphism obj)))

(defmethod aut CategoryObject
  [obj]

  (->Monoid
    (enumerate-automorphisms obj)
    (fn [[a b]]
      (compose a b))
    (identity-morphism obj)))



