(ns locus.elementary.dataflow.functional.decomposition
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.lens.core.lens-type :refer :all])
  (:import (locus.elementary.lens.core.lens_type LensType)))

; Product decompositions in terms of the lattice of partitions
; In the relational model of dataflow we construct a layer of abstraction over
; the topoi of sets and functions. Over the topos of sets we construct the product
; decomposition notion in order to make it easier to deal with memory locations
; modeled by congruences. Over the topos of functions we then deal with congruences
; using relations between product decompositions.
(deftype ProductDecomposition [coll keys components]
  ConcreteObject
  (underlying-set [this] coll))

; Product decompositions can be acquired by lens types
(defmulti to-product-decomposition type)

(defmethod to-product-decomposition ProductDecomposition
  [decomposition])

(defmethod to-product-decomposition LensType
  [^LensType lens]

  (ProductDecomposition.
    (underlying-set lens)
    #{0 1}
    {0 (.active lens)
     1 (.stable lens)}))

; Get the equivalence relations associated with a product decomposition.
; A product decomposition can also be intuited to be a kind of partition system.
(defn get-equivalence-relation
  [^ProductDecomposition decomposition, coll]

  (apply
    intersection
    (map
      (fn [i]
        ((.components decomposition) i))
      coll)))

(defn get-lens-type
  [^ProductDecomposition decomposition, i]

  (->LensType
    (underlying-set decomposition)
    ((.components decomposition) i)
    (get-equivalence-relation decomposition (disj (.keys decomposition) i))))

; Sequence size classifier
(defn equivalence-relation-by-function
  [coll func]

  (->Universal
    (fn [pair]
      (and
        (size-two-seq? pair)
        (let [[a b] pair]
          (and
            (coll a)
            (coll b)
            (= (func a) (func b))))))))

(defn sequence-size-classifier
  [n]

  (->Universal
    (fn [coll]
      (and
        (seq? coll)
        (= (count coll) n)))))

(defn sequence-equivalence-relation
  [n i]

  (equivalence-relation-by-function
    (sequence-size-classifier n)
    (fn [coll]
      (nth coll i))))

(defn sequence-decomposition
  [n]

  (ProductDecomposition.
    (sequence-size-classifier n)
    (set (range n))
    (fn [i]
      (sequence-equivalence-relation n i))))

(defn cartesian-product-decomposition
  [& colls]

  (let [rel (apply cartesian-product colls)]
    (ProductDecomposition.
     rel
     (set (range (count colls)))
     (fn [i]
       (equivalence-relation-by-function rel (fn [coll] (nth coll i)))))))

; Define a classifier for the sizes of vectors
(defn vector-size-classifier
  [n]

  (->Universal
    (fn [coll]
      (and
        (vector? coll)
        (= (count coll) n)))))

(defn vector-equivalence-relation
  [n i]

  (equivalence-relation-by-function
    (vector-size-classifier n)
    (fn [coll]
      (nth coll i))))

(defn vector-decomposition
  [n]

  (ProductDecomposition.
    (sequence-size-classifier n)
    (set (range n))
    (fn [i]
      (vector-equivalence-relation n i))))

; Classify maps by keys
(defn map-keys-classifier
  [key-set]

  (->Universal
    (fn [coll]
      (and
        (map? coll)
        (equal-universals? (keys coll) key-set)))))

(defn map-keys-decomposition
  [key-set]

  (let [classifier (map-keys-classifier key-set)]
    (ProductDecomposition.
     classifier
     key-set
     (fn [key]
       (equivalence-relation-by-function
         classifier
         (fn [coll]
           (get coll key)))))))

; Here we will attempt to create classes of matrices for our own use
(defn matrix-size-classifier
  [number-of-rows number-of-columns]

  (fn [coll]
    (and
      (vector? coll)
      (= (count coll) number-of-rows)
      (every?
        (fn [i]
          (and
            (vector? i)
            (= (count i) number-of-columns)))
        coll))))

(defn matrix-coordinates-decomposition
  [number-of-rows number-of-columns]

  (let [classifier (matrix-size-classifier number-of-rows number-of-columns)]
    (ProductDecomposition.
     classifier
     (seqable-cartesian-product
       (seqable-interval 0 number-of-rows)
       (seqable-interval 0 number-of-columns))
     (fn [[i j]]
       (equivalence-relation-by-function
         classifier
         (fn [coll]
           (get-in coll [i j])))))))