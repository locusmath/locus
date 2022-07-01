(ns locus.elementary.category.adjoint.functors
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]))

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