(ns locus.partial.copresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.category.concrete.categories :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.partial.quiver.object :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.category.core.morphism Functor)))

; A functor F : C -> Sets[Part] is a functor from a category to the category of sets and partial
; functions. The category Sets[Part] of sets and partial functions is a concrete category,
; where each set is adjoined an extra zero element which is outputted when the values of a
; partial function don't exist. It follows therefore that as a functor to a concrete category,
; it is a structure copresheaf. So it will be handled as part of the presheaf theory framework
; which is the hallmark of Locus.
(deftype PartialCopresheaf [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] partial-sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive PartialCopresheaf :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Implementing these multimethods integrates partial copresheaves into the structure presheaf framework
(defmethod get-object PartialCopresheaf
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism PartialCopresheaf
  [functor x]

  ((first-function functor) x))

(defmethod get-set PartialCopresheaf
  [functor x]

  (nullable-set (get-object functor x)))

(defmethod get-function PartialCopresheaf
  [functor x]

  (nullable-function (get-morphism functor x)))

; Partial copresheaves are structure copresheaves over an index category
(defmethod index PartialCopresheaf
  [^PartialCopresheaf functor] (.-category functor))

; Generalized mechanisms for converting objects into partial copresheaves
(defmulti to-partial-copresheaf type)

(defmethod to-partial-copresheaf PartialCopresheaf
  [functor] functor)

(defmethod to-partial-copresheaf :locus.base.logic.core.set/universal
  [coll]

  (PartialCopresheaf
    (thin-category (weak-order [#{0}]))
    (fn [obj]
      coll)
    (fn [arrow]
      (partial-identity-function coll))))

(defmethod to-partial-copresheaf :locus.partial.mapping.function/partial-function
  [func]

  (PartialCopresheaf.
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

(defmethod to-partial-copresheaf Copresheaf
  [copresheaf]

  (PartialCopresheaf.
    (index copresheaf)
    (partial get-set copresheaf)
    (fn [arrow]
      (to-partial-function (get-function copresheaf arrow)))))

(defmethod to-partial-copresheaf :default
  [copresheaf] (to-partial-copresheaf (to-copresheaf copresheaf)))

; Conversion routines
(defmethod to-functor PartialCopresheaf
  [functor]

  (Functor.
    (index functor)
    partial-sets
    (partial get-object functor)
    (partial get-morphism functor)))

(defmethod to-copresheaf PartialCopresheaf
  [functor]

  (Copresheaf.
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Partial copresheaves produce partial actions
(comment
  (defn get-pset-by-object
   [partial-functor object]

   (let [cat (index partial-functor)]
     (->PSet
       (endomorphism-monoid cat object)
       (get-object partial-functor object)
       (fn [arrow]
         (get-morphism partial-functor arrow))))))

; A mechanism for automatically creating triangles in the category of sets and partial functions
(defn partial-triangle
  [f g]

  (PartialCopresheaf.
    (thin-category (weak-order [#{0} #{1} #{2}]))
    (fn [obj]
      (case obj
        0 (source-object g)
        1 (target-object g)
        2 (target-object f)))
    (fn [[a b]]
      (case [a b]
        [0 0] (partial-identity-function (source-object g))
        [0 1] g
        [0 2] (compose f g)
        [1 1] (partial-identity-function (target-object g))
        [1 2] f
        [2 2] (partial-identity-function (target-object f))))))

; Ontology of partial functors
(defn partial-copresheaf?
  [x]

  (= (type x) PartialCopresheaf))

(defn object-partial-copresheaf?
  [x]

  (and
    (partial-copresheaf? x)
    (let [cat (index x)]
      (= (count (objects cat))
         (count (morphisms cat))
         1))))

(defn function-partial-copresheaf?
  [x]

  (and
    (partial-copresheaf? x)
    (let [cat (index x)]
      (and
        (= (count (objects cat)) 2)
        (total-order-category? cat)))))

(defn partial-chain?
  [x]

  (and
    (partial-copresheaf? x)
    (total-order-category? (index x))))

(defn partial-triangle?
  [x]

  (and
    (partial-copresheaf? x)
    (total-order-category? (index x))
    (= (count (objects (index x))) 3)))

(defn partial-diamond?
  [x]

  (and
    (partial-copresheaf? x)
    (diamond-category? (index x))))

(defn partial-span?
  [x]

  (and
    (partial-copresheaf? x)
    (let [cat (index x)]
      (and
        (n-span-category? cat)
        (= (count (objects cat)) 3)))))

(defn partial-cospan?
  [x]

  (and
    (partial-copresheaf? x)
    (let [cat (index x)]
      (and
        (n-cospan-category? cat)
        (= (count (objects cat)) 3)))))