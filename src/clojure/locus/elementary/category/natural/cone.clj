(ns locus.elementary.category.natural.cone
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.natural.transformation :refer :all])
  (:import (locus.elementary.category.core.morphism Functor)))

; A cone is a natural transformation from a constant functor to some other functor.
; They can be used to define limits in a category-theory framework.
(deftype Cone [source-object target-functor func]
  AbstractMorphism
  (source-object [this]
    (constant-functor
      (source-object target-functor)
      (target-object target-functor)
      source-object))
  (target-object [this] target-functor)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Cone :locus.elementary.category.natural.transformation/cone)

; Index categories of cone natural transformations
(defmethod index Cone
  [^Cone cone]

  (ordered-pair-product-category (source-object (target-object cone))))

; Convert cones into functors or natural transformations
(defmethod to-natural-transformation Cone
  [^Cone cone]

  (->NaturalTransformation
    (source-object cone)
    (target-object cone)
    (.-func cone)))

(defmethod to-functor Cone
  [^Cone cone]

  (->Functor
    (index cone)
    (target-object (target-object cone))
    (partial get-object cone)
    (partial get-morphism cone)))

; Conversion routines that produce cones
(defmulti to-cone type)

(defmethod to-cone Cone
  [^Cone cone] cone)

; Ontology of cones
(defn cone?
  [cone]

  (= (type cone) Cone))
