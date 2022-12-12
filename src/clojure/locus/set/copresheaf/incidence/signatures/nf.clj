(ns locus.set.copresheaf.incidence.signatures.nf
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.numeric-sequence.rp :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.copresheaf.incidence.system.multiclan :refer :all]
            [locus.set.copresheaf.incidence.system.clan :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.copresheaf.incidence.system.multifamily :refer :all]))

; Suppose that we have a set of multisets. Then each multiset in the multiset system is associated
; to an additive partition. This produces a multiset of additive partitions, and so this naturally
; produces multisets of multisets of natural numbers. In this file, we will describe how we can
; handle such nested collections of natural numbers.

(def all-signatures
  (partial umap signature))

(defn numeric-multiclan?
  [coll]

  (and
    (multiclan? coll)
    (every? natural-multiset? coll)))

(defn numeric-clan?
  [coll]

  (and
    (clan? coll)
    (every? natural-multiset? coll)))

(defn numeric-family?
  [coll]

  (and
    (multifamily? coll)
    (every? natural-number? (apply union coll))))

(defn numeric-family?
  [coll]

  (and
    (family-of-universals? coll)
    (every? natural-number? (apply union coll))))

; Additive partitions
(defn multiclan-of-additive-partitions?
  [coll]

  (and
    (multiset? coll)
    (every? additive-partition? coll)))

(defn family-of-additive-partitions?
  [coll]

  (and
    (universal? coll)
    (every? additive-partition? coll)))

; Numeric progressions
(defn numeric-progression?
  [coll]

  (and
    (progression-clan? coll)
    (every? natural-multiset? coll)))

(defn positive-integer-progression?
  [coll]

  (and
    (progression-clan? coll)
    (every? additive-partition? coll)))

; Range partitions
(defn range-partition?
  [coll]

  (and
    (set-partition? coll)
    (= (apply union coll)
       (set (range (apply + (map count coll)))))))

(defn consecutive-range-partition?
  [coll]

  (and
    (range-partition? coll)
    (every? natural-interval? coll)))

; Non crossing partitions are a very important part of combinatorics
(defn crossing-pair?
  [[a b]]

  (letfn [(partially-enclosed-by? [min max coll]
            (not
              (every?
                (fn [i]
                  (not (<= min i max)))
                coll)))]
    (let [mina (apply min a)
         maxa (apply max a)
         minb (apply min b)
         maxb (apply max b)]
     (and
       (partially-enclosed-by? mina maxa b)
       (partially-enclosed-by? minb maxb a)))))

(defn noncrossing-range-partition?
  [coll]

  (and
    (range-partition? coll)
    (every?
      (fn [pair]
        (not (crossing-pair? (seq pair))))
      (selections coll 2))))

(defn noncrossing-closure
  [partition]

  (letfn [(get-crossing-pair [partition]
            (first
              (filter
                (fn [pair]
                  (crossing-pair? (seq pair)))
                (selections partition 2))))
          (remove-crossing-pair [partition pair]
            (conj
              (difference partition pair)
              (apply union pair)))]
    (loop [current-partition partition]
      (let [current-crossing-pair (get-crossing-pair current-partition)]
        (if (nil? current-crossing-pair)
          current-partition
          (recur
            (remove-crossing-pair current-partition current-crossing-pair)))))))

(defn join-noncrossing-partitions
  [& partitions]

  (noncrossing-closure
    (apply
      join-set-partitions
      partitions)))

