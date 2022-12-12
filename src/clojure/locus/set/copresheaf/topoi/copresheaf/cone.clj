(ns locus.set.copresheaf.topoi.copresheaf.cone
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.natural.transformation :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.morphism :refer :all])
  (:import (locus.algebra.category.core.morphism Functor)))

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

