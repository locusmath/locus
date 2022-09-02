(ns locus.elementary.category.path.composable-path
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.object.category-object :refer :all]
            [locus.elementary.category.morphism.category-morphism :refer :all]))

; A composable path in a category is a pair of morphisms g : A -> B and f : B -> C
; such that the composition f*g exists. In the copresheaf formulation of categories,
; composable paths are the third set of elements aside from objects and morphisms,
; which form the domain of the composition function of the category.
(deftype ComposablePath [category f g])

; Convert something in to a composable path
(defmulti to-composable-path type)

(defmethod to-composable-path ComposablePath
  [^ComposablePath path] path)

; Get the morphism components of a path as category morphism objects
(defn premorphism
  [^ComposablePath path]

  (->CategoryMorphism (.-category path) (.-g path)))

(defn postmorphism
  [^ComposablePath path]

  (->CategoryMorphism (.-category path) (.-f path)))

; Get the composition of a composable path
(defn get-composition
  [^ComposablePath path]

  (let [category (.-category path)
        f (.-f path)
        g (.-g path)]
    (category (list f g))))

; Ontology of composable paths
(defn composable-path?
  [obj]

  (= (type obj) ComposablePath))