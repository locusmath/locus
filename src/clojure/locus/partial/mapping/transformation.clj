(ns locus.partial.mapping.transformation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.effects.global.transformation :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer [restrict-partition projection]]
            [locus.partial.mapping.function :refer :all])
  (:import (clojure.lang IPersistentMap)
           (locus.base.effects.global.transformation Transformation)))

; Partial transformations are partial unary-algebras. As a consequence, they can be handled topos
; theoretically as part of the topos theoretic framework of universal partial algebra. In
; particular, using this framework we can define products, coproducts, subobjects, and
; quotients for partial transformations as well as morphisms of partial transformations
; considered as structured sets. These leads to the category of partial transformations and
; partial unary algebra homomorphisms between them. Separately, partial transformations can also
; be considered to be morphisms in the category of sets and partial functions.
(deftype PartialTransformation
  [domain coll func]

  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PartialTransformation :locus.partial.mapping.function/partial-transformation)

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
(comment
  (defn partial-transformation-preorder
   [func]

   (cl preorder? (underlying-relation func))))

; Special types of partial transformations
(defn empty-partial-transformation
  [coll]

  (PartialTransformation.
    #{}
    coll
    {}))

; Create a partial transformation from a binary relation
(defn relational-partial-transformation
  ([rel]
   (let [vertices (apply union (map set rel))]
     (relational-partial-transformation vertices rel)))
  ([coll rel]
   (let [my-mapping (into {} (map vec rel))]
     (->PartialTransformation
       (set (keys my-mapping))
       coll
       my-mapping))))

; Conversion routines
(defmulti to-partial-transformation type)

(defmethod to-partial-transformation PartialTransformation
  [^PartialTransformation transformation] transformation)

(defmethod to-partial-transformation IPersistentMap
  [coll]

  (let [all-values (union (set (keys coll)) (set (vals coll)))
        source-values (set (keys coll))]
    (PartialTransformation.
      source-values
      all-values
      (fn [i]
        (get coll i)))))

(defmethod to-partial-transformation :locus.base.logic.core.set/universal
  [coll] (relational-partial-transformation coll))

(defmethod to-partial-transformation :locus.base.logic.structure.protocols/set-function
  [func]

  (let [all-values (union (inputs func) (outputs func))]
    (->PartialTransformation
      (inputs func)
      all-values
      (fn [x]
        (func x)))))

(defmethod to-partial-transformation :locus.base.logic.structure.protocols/transformation
  [transformation]

  (->PartialTransformation (inputs transformation) (inputs transformation) transformation))

(defmethod to-partial-transformation :locus.partial.mapping.function/partial-transformation
  [func]

  (let [all-values (union (source-object func) (target-object func))]
    (->PartialTransformation
      (defined-domain func)
      all-values
      (fn [x]
        (func x)))))

(defmethod to-partial-transformation :default
  [func]

  (to-partial-transformation (underlying-function func)))

; Convert partial transformations into partial set functions
(defmethod to-partial-function PartialTransformation
  [func]

  (->PartialFunction
    (defined-domain func)
    (source-object func)
    (target-object func)
    (fn [i]
      (func i))))

; Products and coproducts in the category of partial transformations
(defmethod product PartialTransformation
  [& args]

  (->PartialTransformation
    (apply product (map defined-domain args))
    (apply product (map target-object args))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth args i) v))
        coll))))

(defmethod coproduct PartialTransformation
  [& args]

  (->PartialTransformation
    (apply coproduct (map defined-domain args))
    (apply coproduct (map target-object args))
    (fn [[i v]]
      (list i ((nth args i) v)))))

; Subobjects of partial transformations
(defn partial-subtransformation?
  [transformation new-domain new-outputs]

  (and
    (superset? (list new-domain new-outputs))
    (every?
      (fn [input]
        (contains? new-outputs (transformation input)))
      new-domain)))

(defn partial-subtransformation
  [transformation new-domain new-outputs]

  (->PartialTransformation
    new-domain
    new-outputs
    transformation))

(defn existence-reduction
  [transformation new-domain]

  (->PartialTransformation
    new-domain
    (target-object transformation)
    transformation))

(defn restrict-partial-transformation
  [transformation new-coll]

  (->PartialTransformation
    (intersection (defined-domain transformation) new-coll)
    new-coll
    transformation))

; Congruences of partial transformations
(defn partial-transformation-congruence?
  [transformation partition]

  (let [defined-partition (restrict-partition
                            partition
                            (defined-domain transformation))
        defined-function (->SetFunction
                           (defined-domain transformation)
                           (target-object transformation)
                           transformation)]
    (io-relation? defined-function defined-partition partition)))

(defn quotient-partial-transformation
  [transformation partition]

  (->PartialTransformation
    (restrict-partition
      partition
      (defined-domain transformation))
    partition
    (fn [part]
      (projection partition (transformation (first part))))))

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