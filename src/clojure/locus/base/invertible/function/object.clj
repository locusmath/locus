(ns locus.base.invertible.function.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all])
  (:import (locus.base.logic.limit.product CartesianCoproduct)
           (clojure.lang IPersistentMap)))

; An invertible function is a function f: A -> B with a corresponding inverse function
; f^(-1) : B -> A. It is still treated as a member of the topos of sets and functions
; in this class instead of being given its own topos. It is equivalently an isomorphism
; in the topos Sets.
(deftype InvertibleFunction [in out forward backward]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  ConcreteObject
  (underlying-set [this] (CartesianCoproduct. [in out]))

  Invertible
  (inv [this]
    (InvertibleFunction. out in backward forward))

  clojure.lang.IFn
  (invoke [this obj]
    (forward obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive InvertibleFunction :locus.base.logic.structure.protocols/invertible-set-function)

; Conversion routines
(defmulti to-invertible-function type)

(defmethod to-invertible-function :locus.base.logic.structure.protocols/invertible-set-function
  [func] func)

(defmethod to-invertible-function :locus.base.logic.structure.protocols/set-function
  [func]

  (if (not (invertible? func))
    (throw (new IllegalArgumentException))
    (->InvertibleFunction
      (inputs func)
      (outputs func)
      (fn [i]
        (func i))
      (fn [x]
        (first (fiber func x))))))

(defmethod to-invertible-function IPersistentMap
  [coll]

  (if (not (distinct-seq? (vals coll)))
    (throw (new IllegalArgumentException))
    (->InvertibleFunction
      (set (keys coll))
      (set (vals coll))
      coll
      (apply array-map (apply concat (map reverse (seq coll)))))))

; Composition and identities in the subcategory of invertible functions
(defmethod compose* InvertibleFunction
  [f g]

  (InvertibleFunction.
    (outputs g)
    (inputs f)
    (comp (.forward f) (.forward g))
    (comp (.backward f) (.backward g))))

(defn invertible-identity-function
  [coll]

  (InvertibleFunction.
    coll
    coll
    identity
    identity))

; Invertible pair functions
(defn invertible-pair-function
  [a b]

  (->InvertibleFunction
    #{a}
    #{b}
    (constantly b)
    (constantly a)))

; Products and coproducts in the subcategory of invertible functions
(defmethod product InvertibleFunction
  [& functions]

  (InvertibleFunction.
    (apply cartesian-product (map inputs functions))
    (apply cartesian-product (map outputs functions))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth functions i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((.backward (nth functions i)) v))
        coll))))

(defmethod coproduct InvertibleFunction
  [& functions]

  (InvertibleFunction.
    (apply cartesian-coproduct (map inputs functions))
    (apply cartesian-coproduct (map outputs functions))
    (fn [[i v]]
      (list i ((nth functions i) v)))
    (fn [[i v]]
      (list i ((.backward (nth functions i)) v)))))