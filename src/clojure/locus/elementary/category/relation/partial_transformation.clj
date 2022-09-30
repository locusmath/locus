(ns locus.elementary.category.relation.partial-transformation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.elementary.category.relation.partial-function :refer :all])
  (:import (clojure.lang PersistentArrayMap PersistentHashSet PersistentHashMap)))

; A partial transformation is an endomorphism in the category of sets and
; partial functions. In our ontology, we define partial transformations as special
; types of partial set functions by using derive. Partial transformations are distinguished
; from ordinary functions by the fact that they are only defined on a subset of their inputs.
(deftype PartialTransformation
  [domain coll func]

  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] coll)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PartialTransformation :locus.elementary.category.relation.partial-function/partial-transformation)

; Defined domains of partial transformations
(defmethod defined-domain PartialTransformation
  [^PartialTransformation func]

  (.domain func))

; Composition and identities in terms of partial transformations
(defn identity-partial-transformation
  [coll]

  (PartialTransformation.
    coll
    coll
    (fn [x]
      x)))

(defmethod compose* PartialTransformation
  [a b]

  (let [new-coll (set
                   (filter
                     (fn [i]
                       (boolean
                         ((defined-domain a) (b i))))
                     (.coll b)))]
    (PartialTransformation.
      new-coll
      (source-object b)
      (comp (.func a) (.func b)))))

; The action preorder of a partial transformation
(defn partial-transformation-preorder
  [func]

  (cl preorder? (underlying-relation func)))

; Partial transformation producers
(defn empty-partial-transformation
  [coll]

  (PartialTransformation.
    #{}
    coll
    {}))

(defn map-to-partial-transformation
  [coll]

  (let [all-values (union (set (keys coll)) (set (vals coll)))
        source-values (set (keys coll))]
    (PartialTransformation.
      source-values
      all-values
      (fn [i]
        (get coll i)))))

(defn relational-partial-transformation
  [coll rel]

  (let [source-values (relation-domain rel)]
    (PartialTransformation.
      source-values
      coll
      (fn [i]
        (call rel i)))))

(defn relation-to-partial-transformation
  [rel]

  (relational-partial-transformation (vertices rel) rel))

; Conversion multimethod
(defmulti to-partial-transformation type)

(defmethod to-partial-transformation PartialTransformation
  [func] func)

(defmethod to-partial-transformation PersistentArrayMap
  [coll] (map-to-partial-transformation coll))

(defmethod to-partial-transformation PersistentHashMap
  [coll] (map-to-partial-transformation coll))

; Convert partial transformations into partial set functions
(defmethod to-partial-function PartialTransformation
  [func]

  (->PartialFunction
    (defined-domain func)
    (source-object func)
    (target-object func)
    (fn [i]
      (func i))))

; Join and meet of partial transformations
(defn joinable-partial-transformations?
  [a b]

  (every?
    (fn [i]
      (= (a i) (b i)))
    (intersection (defined-domain a) (defined-domain b))))

(defn meet-partial-transformations
  [& transformations]

  (when (not (empty? transformations))
    (let [common-domain (filter
                          (fn [i]
                            (equal-seq?
                              (map
                                (fn [transformation]
                                  (transformation i))
                                transformations)))
                          (apply
                            intersection
                            (map defined-domain transformations)))]
      (PartialTransformation.
        common-domain
        (apply intersection (map target-object transformations))
        (fn [i]
          ((.func (first transformations)) i))))))

(defn join-partial-transformations
  [& transformations]

  (letfn [(to-map [transformation]
            (apply
              merge
              (map
                (fn [i]
                  {i (transformation i)})
                (defined-domain transformation))))]
    (PartialTransformation.
      (apply union (map defined-domain transformations))
      (apply union (map target-object transformations))
      (apply merge (map to-map transformations)))))