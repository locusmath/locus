(ns locus.base.sequence.numeric.rp
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.numeric.ac :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]))

; Consider a list (a,b,c,..) then a list can also be defined as a function f : I -> X, where I
; is some index ordinal. Then the elements of I which are natural numbers 0,1,2,... form a
; range which is partitioned by the kernel of f. This leads to the ontology of range partitions.
; We say that sequences are classified up to isomorphism by their range partitions just as
; multisets are classified up to isomorphism by their signatures.

; Range partitions
(defn all-range-partitions
  [n]

  (set (enumerate-set-partitions (set (range n)))))

(defn range-partitions-upto
  [n]

  (apply
    union
    (map
      (fn [i]
        (all-range-partitions i))
      (range (inc n)))))

; Consecutive range partitions
; Create a consecutive range partition from an additive compositions
(defn consecutive-range-partition
  [coll]

  (set
    (map
      (fn [i]
        (set
          (let [start-index (apply + (take i coll))]
            (range start-index (+ start-index (nth coll i))))))
      (range (count coll)))))

(defn consecutive-range-partitions
  [n]

  (map
    consecutive-range-partition
    (all-compositions n)))

; Ordering
(defn restrict-range-partition
  [partition coll]

  (let [ordered-coll (sort <= coll)
        indexes (into
                  {}
                  (map
                    (fn [i]
                      [(nth ordered-coll i) i])
                    (range (count ordered-coll))))]
    (set
      (map
        (fn [part]
          (set
            (map
              (partial get indexes)
              part)))
        (restrict-partition partition coll)))))

(defn immediate-range-subpartitions
  [range-partition]

  (let [size (apply + (map count range-partition))]
    (set
      (map
        (fn [i]
          (set
            (for [new-coll (map
                             (fn [coll]
                               (for [n coll
                                     :when (not= i n)]
                                 (if (<= n i)
                                   n
                                   (dec n))))
                             range-partition)
                  :when (not (empty? new-coll))]
              (set new-coll))))
        (range size)))))

(defn all-range-subpartitions
  [range-partition]

  (set
    (map
      (fn [coll]
        (restrict-range-partition range-partition coll))
      (power-set (apply union range-partition)))))

(def covering-range-partition?
  (assoc (->Universal
           (fn [[a b]]
             (contains? (immediate-range-subpartitions b) a)))
    :arities #{2}))

