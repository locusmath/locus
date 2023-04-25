(ns locus.set.mapping.general.core.subquotient
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.sub.mapping.function :refer :all]
            [locus.set.mapping.function.core.functor :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all])
  (:import (locus.set.quiver.unary.core.morphism Diamond)))

; Partial partitions of a set
(defn number-of-partial-partitions
  [n]

  (bell-number (inc n)))

(defn partial-partitions
  [coll]

  (apply
    union
    (map
      (fn [i]
        (set-partitions i))
      (power-set coll))))

(defn partial-equivalence-relation-on?
  [coll rel]

  (and
    (equivalence-relation? rel)
    (superset? (list (vertices rel) coll))))

; The ordering on partial partitions
(defn block-of-partial-partition?
  [coll partition]

  (let [intersections (filter
                        (fn [part]
                          (not (empty? (intersection part coll))))
                        partition)]
    (and
      (not (empty? intersections))
      (let [parent (first intersections)]
        (superset? (list coll parent))))))

(defn partial-subpartition?
  [partition1 partition2]

  (every?
    (fn [part]
      (block-of-partial-partition? part partition2))
    partition1))

(defn partial-subpartitions
  [partition]

  (map
    (fn [coll]
      (apply union coll))
    (apply cartesian-product (map partial-partitions partition))))

(defn covering-partial-partitions
  [partition coll]

  (let [all-elements (apply union partition)
        remaining-elements (difference coll all-elements)]
    (set
      (concat
        (map
          (fn [remaining-element]
            (union #{#{remaining-element}} partition))
          remaining-elements)
        (direct-set-partition-coarsifications partition)))))

; Create a partial projection function from a partial partition
(defn partial-projection-function
  [coll partition]

  (->PartialFunction
    (apply union partition)
    coll
    partition
    (fn [i]
      (projection partition i))))

; Partial partition pairs generalize partition pairs
(defn partial-partition-pair?
  [func in-partition out-partition]

  (let [out-relation (equivalence-relation out-partition)]
    (every?
      (fn [in-part]
        (let [current-image (set-image func in-part)]
          (every?
            (fn [[a b]]
              (out-relation (list a b)))
            (cartesian-power current-image 2))))
      in-partition)))

; Get the subquotient function associated to a partial partition pair
(defn subquotient-function
  [func partition1 partition2]

  (let [coll1 (apply union partition1)
        coll2 (apply union partition2)
        restricted-func (subfunction func coll1 coll2)]
    (quotient-function
      restricted-func
      partition1
      partition2)))

; Pair algebra operations
(defn partial-partition-image
  [func partition]

  (partitionize-family
    (set
      (map
        (fn [i]
          (set-image func i))
        partition))))

(defn partial-partition-inverse-image
  [func partition]

  (set
    (for [i partition
          :let [coll (set-inverse-image func i)]
          :when (not (empty? coll))]
      coll)))

; inclusion relations for subquotients
(defn included-partial-partition-pair?
  [[a b] [c d]]

  (and
    (partial-subpartition? a c)
    (partial-subpartition? b d)))

; Get all partial partition pairs of a function
(defn partial-partition-pairs
  [func]

  (set
    (mapcat
      (fn [output-partition]
        (let [in-partition (partial-partition-inverse-image func output-partition)]
          (map
            (fn [new-in-partition]
              (list new-in-partition output-partition))
            (partial-subpartitions in-partition))))
      (partial-partitions (outputs func)))))

; Aspects of the partial partition pairs system
(defn partial-partition-pairs-ordering
  [func]

  (let [coll (partial-partition-pairs func)]
    (set
      (filter
        (fn [[a b]]
          (included-partial-partition-pair? a b))
        (cartesian-product coll coll)))))

(defn covering-partial-partition-pairs
  [func in-partition out-partition]

  (set
    (concat
      (for [new-in-partition (covering-partial-partitions in-partition (inputs func))
            :when (partial-partition-pair? func new-in-partition out-partition)]
        (list new-in-partition out-partition))
      (map
        (fn [new-out-partition]
          (list in-partition new-out-partition))
        (covering-partial-partitions out-partition (outputs func))))))

(defn partial-partition-pairs-covering
  [func]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list
              (list in-partition out-partition)
              (list new-in-partition new-out-partition)))
          (covering-partial-partition-pairs func in-partition out-partition)))
      (partial-partition-pairs func))))

