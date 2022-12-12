(ns locus.set.mapping.effects.global.transformation
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all])
  (:import (clojure.lang IPersistentMap)))

; Transformations
; A transformation is simply an endomorphism in the topos Sets, which means that it can be composed
; with itself. Transformations are distinguished from general morphisms in Sets by the fact that
; they do not require the specification of two different sets to define them.
(deftype Transformation [coll func]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [coll coll]))

  Object
  (equals [this b]
    (and
      (equal-universals? (.coll this) (.coll ^Transformation b))
      (every?
        (fn [i]
          (= (this i) (b i)))
        coll)))

  clojure.lang.IFn
  (invoke [this obj]
    (func obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Transformation :locus.set.logic.structure.protocols/transformation)

; Automatic conversion of objects to transformations
(defmulti to-transformation type)

(defmethod to-transformation Transformation
  [func] func)

(defmethod to-transformation IPersistentMap
  [coll]

  (let [key-set (set (keys coll))]
    (Transformation.
      key-set
      coll)))

(defmethod to-transformation :locus.set.logic.structure.protocols/set-function
  [func]

  (if (not (equal-universals? (inputs func) (outputs func)))
    (throw (new IllegalArgumentException))
    (Transformation.
      (inputs func)
      (fn [i]
        (func i)))))

(defn numeric-transformation
  [coll]

  (Transformation.
    (->Upto (count coll))
    (fn [i]
      (nth coll i))))

; Identities and composition in the subcategory of transformations
(defn identity-transformation
  [coll]

  (Transformation. coll identity))

(defmethod compose* Transformation
  [a b]

  (Transformation.
    (inputs b)
    (comp (.func a) (.func b))))

; We also need some way of dealing with the products and coproducts
; of transformations which can pretty naturally be defined
(defmethod product Transformation
  [& transformations]

  (Transformation.
    (apply cartesian-product (map inputs transformations))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth transformations i) v))
        coll))))

(defmethod coproduct Transformation
  [& transformations]

  (Transformation.
    (apply cartesian-coproduct (map inputs transformations))
    (fn [[i v]]
      (list i ((nth transformations i) v)))))

; Equal subalgebras
(defn equal-subfunction?
  [func coll]

  (every?
    (fn [i]
      (contains? coll (func i)))
    coll))

(defn equal-subfunctions
  [func]

  (set
    (filter
      (fn [coll]
        (equal-subfunction? func coll))
      (power-set (inputs func)))))

(defn restrict-transformation
  [transformation coll]

  (Transformation.
    coll
    (.func transformation)))

; Equal congruences
(defn equal-congruence?
  [func partition]

  (io-relation? func partition partition))

(defn equal-congruences
  [func]

  (set
    (filter
      (partial equal-congruence? func)
      (enumerate-set-partitions (inputs func)))))

(defn quotient-transformation
  [transformation partition]

  (Transformation.
    partition
    (fn [i]
      (projection partition (transformation (first i))))))

; We need some way of dealing with fixed and moved points
(defn fixed-points
  [transformation]

  (set
    (filter
      (fn [i]
        (= i (transformation i)))
      (inputs transformation))))

(defn moved-points
  [transformation]

  (set
    (filter
      (fn [i]
        (not= i (transformation i)))
      (inputs transformation))))

(defn number-of-fixed-points
  [transformation]

  (count (fixed-points transformation)))

(defn number-of-moved-points
  [transformation]

  (count (moved-points transformation)))

; Lets use this mechanism to get the connected components of a transformation function
(defn transformation-components
  [transformation]

  (partitionize-family
    (set
      (map
        set
        (underlying-relation transformation)))))

; We need to get the index period of a transformation
(defn index-period
  [transformation]

  (letfn [(compute-index-period [first-index second-index]
            [(inc first-index) (- second-index first-index)])]
    (loop [seen-values [transformation]
           cval transformation
           i 1]
      (let [next-val (compose cval transformation)
            j (.indexOf seen-values next-val)]
        (if (not= j -1)
          (compute-index-period j i)
          (recur
            (conj seen-values next-val)
            next-val
            (inc i)))))))

; Test for membership in a lens semigroup
(defn preserved-transformation-congruence?
  [func partition]

  (every?
    (fn [part]
      (every?
        (fn [i]
          (contains? part (func i)))
        part))
    partition))

(defn lens-member-transformation?
  [func active-partition preserved-partition]

  (and
    (equal-congruence? func active-partition)
    (preserved-transformation-congruence? func preserved-partition)))