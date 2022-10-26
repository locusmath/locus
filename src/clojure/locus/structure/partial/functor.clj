(ns locus.structure.partial.functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)))

; A functor F : C -> Sets[Part] is a functor from a category to the category of sets and partial
; functions. The category Sets[Part] of sets and partial functions is a concrete category,
; where each set is adjoined an extra zero element which is outputted when the values of a
; partial function don't exist. It follows therefore that as a functor to a concrete category,
; it is a structure copresheaf. So it will be handled as part of the presheaf foundations
; in Locus.
(deftype PartialFunctor [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] partial-sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive PartialFunctor :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; As partial functors are structure copresheaves they have an underlying structural functor
(defmethod get-object PartialFunctor
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism PartialFunctor
  [functor x]

  ((first-function functor) x))

; As partial functors are structure copresheaves they have underlying presheaves
(defmethod get-set PartialFunctor
  [functor x]

  (nullable-set (get-object functor x)))

(defmethod get-function PartialFunctor
  [functor x]

  (nullable-function (get-morphism functor x)))

; Partial functors are structure copresheaves over an index category
(defmethod index PartialFunctor
  [^PartialFunctor functor] (.-category functor))

; Generalized mechanisms for converting objects into partial functors
(defmulti to-partial-functor type)

(defmethod to-partial-functor PartialFunctor
  [functor] functor)

(defmethod to-partial-functor :locus.base.logic.core.set/universal
  [coll]

  (PartialFunctor.
    (thin-category (weak-order [#{0}]))
    (fn [obj]
      coll)
    (fn [arrow]
      (partial-identity-function coll))))

(defmethod to-partial-functor :locus.elementary.category.partial.function/partial-function
  [func]

  (PartialFunctor.
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object func)
        1 (target-object func)))
    (fn [[a b]]
      (case [a b]
        [0 0] (partial-identity-function (source-object func))
        [1 1] (partial-identity-function (target-object func))
        [0 1] func))))

(defmethod to-partial-functor Copresheaf
  [copresheaf]

  (->PartialFunctor
    (index copresheaf)
    (partial get-set copresheaf)
    (fn [arrow]
      (to-partial-function (get-function copresheaf arrow)))))

(defmethod to-partial-functor :default
  [copresheaf] (to-partial-functor (to-copresheaf copresheaf)))

; Conversion routines
(defmethod to-functor PartialFunctor
  [functor]

  (Functor.
    (index functor)
    partial-sets
    (partial get-object functor)
    (partial get-morphism functor)))

(defmethod to-copresheaf PartialFunctor
  [functor]

  (Copresheaf.
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Ontology of partial functors
(defn partial-functor?
  [x]

  (= (type x) PartialFunctor))