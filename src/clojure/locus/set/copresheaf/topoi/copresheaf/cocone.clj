(ns locus.set.copresheaf.topoi.copresheaf.cocone
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
            [locus.set.copresheaf.topoi.copresheaf.morphism :refer :all]))

; A morphism of copresheaves from a copresheaf into a constant copresheaf
; A set cocone is also a special type of morphism of copresheaves.
(deftype SetCocone [source-functor target-object func]
  AbstractMorphism
  (source-object [this] source-functor)
  (target-object [this]
    (constant-copresheaf (index source-functor) target-object))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Get the index category of a cocone in the topos of sets
(defmethod index SetCocone
  [^SetCocone cocone]

  (category-product t2 (index (source-object cocone))))

; Conversion routines for cocones
(defmethod to-morphism-of-copresheaves SetCocone
  [^SetCocone cocone]

  (->MorphismOfCopresheaves
    (source-object cocone)
    (target-object cocone)
    (.-func cocone)))

(defmethod to-copresheaf SetCocone
  [^SetCocone cocone] (to-copresheaf (to-morphism-of-copresheaves cocone)))

; Create a set coproduct cocone
(defn set-coproduct-cocone
  [& sets]

  (let [target (apply coproduct sets)]
    (->SetCocone
      (nset-copresheaf sets)
      target
      (fn [i]
        (->SetFunction
          (nth sets i)
          target
          (fn [x]
            (list i x)))))))

; Ontology of set cocones
(defn set-cocone?
  [obj]

  (= (type obj) SetCocone))