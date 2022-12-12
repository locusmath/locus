(ns locus.set.copresheaf.topoi.system.partsys
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.copresheaf.dependency.difunction.funpair :refer :all]))

; Sets of set partitions
; This naturally includes the theory of suborders of partition lattices, which
; plays an important role in handling the information determined by a set
; of functions on a common set.
(def partitions-family?
  (power-set set-partition?))

(defn partition-system?
  [coll]

  (and
    (universal? coll)
    (every? set-partition? coll)
    (equal-seq?
      (map
        (fn [partition]
          (apply union partition))
        coll))))

(defn covering-partition-system?
  [coll]

  (unary-family?
    (apply meet-set-partitions coll)))

(defn multiplicative-partition-system?
  [coll]

  (= (apply * (map count coll))
     (count (apply meet-set-partitions coll))))

(defn product-partition-system?
  [coll]

  (let [meet-partition (apply meet-set-partitions coll)]
    (and
      (unary-family? meet-partition)
      (= (apply * (map count coll)) (count meet-partition)))))

(defn get-product-partition-system
  [& colls]

  (let [n (count colls)
        product (apply cartesian-product colls)]
    (map
      (fn [i]
        (set-partition-by #(nth % i) product))
      (range n))))
