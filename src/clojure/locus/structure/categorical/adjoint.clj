(ns locus.structure.categorical.adjoint
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.concrete.categories :refer :all]))

; Morphisms in the category of adjunctions
; An adjunction is defined by a pair of parallel functors:
; F : D -> C
; G : C -> D
(deftype Adjunction [f g]
  AbstractMorphism
  (source-object [this]
    (source-object g))
  (target-object [this]
    (target-object g)))

(defn left-adjoint-functor
  [^Adjunction a]

  (.f a))

(defn right-adjoint-functor
  [^Adjunction b]

  (.g b))

; b : C -> D and a : D -> E
(defmethod compose* Adjunction
  [^Adjunction a, ^Adjunction b]

  (Adjunction.
    (compose (.f b) (.f a))
    (compose (.g a) (.g b))))