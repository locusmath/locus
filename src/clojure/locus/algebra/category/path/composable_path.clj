(ns locus.algebra.category.path.composable-path
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; A composable path in a category is a pair of morphisms g : A -> B and f : B -> C
; such that the composition f*g exists. In the copresheaf formulation of categories,
; composable paths are the third set of elements aside from objects and morphisms,
; which form the domain of the composition function of the category.
(deftype ComposablePath [category f g])

; Convert something in to a composable path
(defmulti to-composable-path type)

(defmethod to-composable-path ComposablePath
  [^ComposablePath path] path)

; A composable path is just a functor F: T_3 -> C
(defmethod to-functor ComposablePath)

(defmethod to-functor ComposablePath
  [^ComposablePath path]

  (path-functor (.-category path) [(.-f path) (.-g path)]))

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