(ns locus.algebra.category.natural.cocone
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.natural.transformation :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.category.core.morphism Functor)))

; A cocone is a natural transformation from a functor to a constant functor.
; They can be used to define colimits in a categorical framework.
(deftype Cocone [source-functor target-object func]
  AbstractMorphism
  (source-object [this] source-functor)

  (target-object [this]
    (constant-functor
      (source-object source-functor)
      (target-object source-functor)
      target-object))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Cocone :locus.algebra.category.natural.transformation/cocone)

; Index categories of cocone natural transformations treated as functors
(defmethod index Cocone
  [^Cocone cocone]

  (ordered-pair-product-category (source-object (source-object cocone))))

; Conversion routines for cocones
(defmethod to-natural-transformation Cocone
  [^Cocone cocone]

  (->NaturalTransformation
    (source-object cocone)
    (target-object cocone)
    (.-func cocone)))

(defmethod to-functor Cocone
  [^Cocone cocone]

  (->Functor
    (index cocone)
    (target-object (source-object cocone))
    (partial get-object cocone)
    (partial get-morphism cocone)))

; Conversion routines that produce cocones
(defmulti to-cocone type)

(defmethod to-cocone Cocone
  [cocone] cocone)

; Ontology of cocones
(defn cocone?
  [cocone]

  (= (type cocone) Cocone))