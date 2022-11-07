(ns locus.elementary.topoi.copresheaf.cone
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.natural.transformation :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.topoi.copresheaf.morphism :refer :all])
  (:import (locus.elementary.category.core.morphism Functor)))

; A morphism of copresheaves from a constant copresheaf to another copresheaf
; A set cone is also a special type of morphism of copresheaves.
(deftype SetCone [source-object target-functor func]
  AbstractMorphism
  (source-object [this]
    (constant-copresheaf (index target-functor) source-object))
  (target-object [this] target-functor)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Get the index category of a cone in the topos of sets
(defmethod index SetCone
  [^SetCone cone]

  (category-product t2 (index (target-object cone))))

; Convert a set cone into a morphism of copresheaves
(defmethod to-morphism-of-copresheaves SetCone
  [^SetCone cone]

  (->MorphismOfCopresheaves
    (source-object cone)
    (target-object cone)
    (.-func cone)))

(defmethod to-copresheaf SetCone
  [^SetCone cone] (to-copresheaf (to-morphism-of-copresheaves cone)))

; Create a set product cone
(defn set-product-cone
  [& sets]

  (let [origin (apply product sets)]
    (->SetCone
      origin
      (nset-copresheaf sets)
      (fn [i]
        (->SetFunction
          origin
          (nth sets i)
          (fn [coll]
            (nth coll i)))))))

; Ontology of set cones
(defn set-cone?
  [obj]

  (= (type obj) SetCone))

