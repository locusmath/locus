(ns locus.elementary.difunction.partition.pair
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer :all]))

; Let Sets^2 be the topos of pairs of sets. Then like every topos of copresheaves, objects of
; Sets^2 are naturally associated to congruence lattices. The congruences of Sets^2, as
; generalized from the topos of Sets are simply ordered pairs of partitions. This file
; defines utility classes and helper functions for such pairs of partitions.

; Partition pairs
(defn partition-pair?
  [p q]

  (= (apply union p) (apply union q)))

(defn direct-product-partitions?
  [a b]

  (every?
   (fn [[i j]]
     (= (count (intersection i j)) 1))
   (cartesian-product a b)))

(defn multiplicative-partitions?
  [a b]

  (every?
   (fn [[i j]]
     (not (zero? (count (intersection i j)))))
   (cartesian-product a b)))

(defn uniform-multiplicative-partitions?
  [a b]

  (equal-seq?
   (map
    (fn [[i j]]
      (count (intersection i j)))
    (cartesian-product a b))))

(defn covering-partitions?
  [a b]

  (every?
   (fn [[i j]]
     (<= (count (intersection i j)) 1))
   (cartesian-product a b)))

(defn independent-partitions?
  [a b]

  (singular-universal? (join-set-partitions a b)))

(def complementary-partitions?
  (intersection
   covering-partitions?
   independent-partitions?))

(defn permutable-partitions?
  [p1 p2]

  (let [p3 (join-set-partitions p1 p2)]
    (every?
     (fn [part]
       (multiplicative-partitions?
        (restrict-partition p1 part)
        (restrict-partition p2 part)))
     p3)))
