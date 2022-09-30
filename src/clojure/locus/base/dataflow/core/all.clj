(ns locus.base.dataflow.core.all
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.object :refer :all]))

; Product decomposed set
; A product decomposed set is basically like an ordinary set except that it has an indexed
; family of partitions associated to it. Each of these partitions is associated with a key
; and it can be accessed with the accessor function. As a consequence, we can also fairly
; easily get the intersection equivalence relation from a family of keys. This allows
; us to treat a set like a product type, so that we can provide a functional model of
; dataflow relations in a topos.
(deftype ProductDecomposedSet [coll keys func]
  ConcreteObject
  (underlying-set [this] coll)

  clojure.lang.IFn
  (invoke [this arg]
    (coll arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ProductDecomposedSet :locus.base.logic.core.set/universal)

; Get key values for a product decomposition
(defn get-key-values
  [coll element keys]

  (map
    (fn [key]
      ((.func ^ProductDecomposedSet coll) element key))
    keys))

; Component partitions
(deftype ComponentPartition [coll keys]
  ConcreteObject
  (underlying-set [this]
    (underlying-set coll))

  StructuredFunctionalPartition
  (classifying-function [this]
    (fn [i]
      (get-key-values coll i keys))))

(derive ComponentPartition :locus.base.partition.core.object/functional-partition)

(defn get-partition
  [coll keys]

  (ComponentPartition. coll keys))

; Product decomposition
(defn product-decomposition
  [& colls]

  (ProductDecomposedSet.
    (->CartesianProduct colls)
    (set (range (count colls)))
    (fn [v i]
      (nth v i))))

(defn sequence-size-classifier
  [n]

  (->Universal
    (fn [coll]
      (and
        (seq? coll)
        (= (count coll) n)))))

(defn sequence-decomposition
  [n]

  (->ProductDecomposedSet
    (sequence-size-classifier n)
    (set (range n))
    (fn [coll i]
      (nth coll i))))

; Vector decomposition
(defn vector-size-classifier
  [n]

  (->Universal
    (fn [coll]
      (and
        (vector? coll)
        (= (count coll) n)))))

(defn vector-decomposition
  [n]

  (->ProductDecomposedSet
    (vector-size-classifier n)
    (set (range n))
    (fn [coll i]
      (nth coll i))))

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

  (ProductDecomposedSet.
    (map-keys-classifier key-set)
    (set key-set)
    (fn [coll i]
      (get coll i))))

; Matrix decomposition
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
    (ProductDecomposedSet.
      classifier
      (product
        (->Upto number-of-rows)
        (->Upto number-of-columns))
      (fn [coll [i j]]
        (get-in coll [i j])))))

; Product decomposed function
; Functions between product decomposed sets, with their own overloaded image methods for dealing
; with the partition images created by slot systems.
(deftype ProductDecomposedFunction [in out func rel]
  ConcreteMorphism
  (inputs [this]
    (underlying-set in))
  (outputs [this]
    (underlying-set out))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [in out]))

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive ProductDecomposedFunction :locus.base.logic.structure.protocols/set-function)

(defn relational-flow
  [rel coll]

  (apply
    union
    (for [[a b] rel
         :when (superset? (list a coll))]
     b)))

(defmethod image [ProductDecomposedFunction ComponentPartition]
  [^ProductDecomposedFunction func, ^ComponentPartition partition]

  (let [source-decomposition (.-in func)
        partition-decomposition (.-coll partition)]
    (when (not= source-decomposition partition-decomposition)
      (throw (new IllegalArgumentException))
      (let [rel (.-rel func)
            source-keys (.-keys partition)
            new-keys (rel source-keys)]
        (ComponentPartition.
          (.-out func)
          new-keys)))))

