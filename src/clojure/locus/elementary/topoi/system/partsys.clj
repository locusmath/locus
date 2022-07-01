(ns locus.elementary.topoi.system.partsys
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.difunction.core.funpair :refer :all]))

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
