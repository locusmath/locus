(ns locus.set.copresheaf.dependency.difunction.partpair
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]))

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
