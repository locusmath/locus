(ns locus.elementary.action.effects.transformation
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.diamond.core.object :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)
           (clojure.lang PersistentArrayMap PersistentHashMap)))

; We need some special way of dealing with transformations of sets
(deftype Transformation [coll func]
  java.lang.Object
  (equals [this b]
    (and
      (equal-universals? (.coll this) (.coll ^Transformation b))
      (every?
        (fn [i]
          (= (this i) (b i)))
        coll)))

  ConcreteObject
  (underlying-set [this]
    coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this obj]
    (func obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; We need another constructor of transformations
(defn numeric-transformation
  [coll]

  (Transformation.
    (seqable-interval 0 (count coll))
    (fn [i]
      (nth coll i))))

; A generic routine for array maps and hash maps
(defn map->transformation
  [coll]

  (Transformation. (set (keys coll)) coll))

; We also need a general method for dealing with conversions
(defmulti to-transformation type)

(defmethod to-transformation PersistentArrayMap
  [coll] (map->transformation coll))

(defmethod to-transformation PersistentHashMap
  [coll] (map->transformation coll))

(defmethod to-transformation Transformation
  [func] func)

; Identity transformations are a basic unit of transformation theory
(defn identity-transformation
  [coll]

  (Transformation. coll identity))

; Visualisation
(defmethod visualize Transformation
  [func] (visualize (underlying-function func)))

; Composition
(defmethod compose* Transformation
  [a b] (Transformation. (.coll b) (comp (.func a) (.func b))))

; Thi demonstrates the role of transformations in the topos of functions
(defn subtransformation-morphism
  [func coll]

  (inclusion-diamond func coll coll))

(defn transformation-preorder
  [func]

  (cl preorder? (underlying-relation func)))

(defn restrict-transformation
  [transformation coll]

  (Transformation. coll (.func transformation)))

; We need some way of getting subtransformations which we can
; distinguish from the subfunctions of topos theory.
(defn subtransformation?
  [func coll]

  (every?
    (fn [i]
      (contains? coll (func i)))
    coll))

(defn subtransformations
  [func]

  (set
    (filter
      (fn [coll]
        (subtransformation? func coll))
      (power-set (underlying-set func)))))

(defmethod sub Transformation
  [func]

  (Lattice.
    (subtransformations func)
    union
    intersection))

; We also need some way to deal with congruences of transformations
(defn transformation-congruence?
  [func partition]

  (let [partition-relation (equivalence-relation partition)]
    (every?
      (fn [in-part]
        (let [current-image (set-image func in-part)]
          (every?
            (fn [[a b]]
              (partition-relation (list a b)))
            (cartesian-power current-image 2))))
      partition)))

(defn transformation-congruences
  [func]

  (set
    (filter
      (partial transformation-congruence? func)
      (enumerate-set-partitions (underlying-set func)))))

(defmethod con Transformation
  [func]

  (Lattice.
    (transformation-congruences func)
    join-set-partitions
    meet-set-partitions))

; Quotient transformation
(defn quotient-transformation
  [transformation partition]

  (Transformation.
    partition
    (fn [i]
      (projection partition (transformation (first i))))))

; We also need some way of dealing with the products and coproducts
; of transformations which can pretty naturally be defined
(defmethod product Transformation
  [& transformations]

  (Transformation.
    (apply cartesian-product (map underlying-set transformations))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth transformations i) v))
        coll))))

(defmethod coproduct Transformation
  [& transformations]

  (Transformation.
    (apply cartesian-coproduct (map underlying-set transformations))
    (fn [[i v]]
      (list i ((nth transformations i) v)))))

; We need some way of dealing with fixed and moved points
(defn fixed-points
  [transformation]

  (set
    (filter
      (fn [i]
        (= i (transformation i)))
      (underlying-set transformation))))

(defn moved-points
  [transformation]

  (set
    (filter
      (fn [i]
        (not= i (transformation i)))
      (underlying-set transformation))))

(defn number-of-fixed-points
  [transformation]

  (count (fixed-points transformation)))

(defn number-of-moved-points
  [transformation]

  (count (moved-points transformation)))

; Connected components of a transformation
(defn transformation-components
  [transformation]

  (weak-connectivity (underlying-relation transformation)))

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
    (transformation-congruence? func active-partition)
    (preserved-transformation-congruence? func preserved-partition)))

; Special classes of total transformations
(defn total-transformation?
  [func]

  (= (type func) Transformation))




















