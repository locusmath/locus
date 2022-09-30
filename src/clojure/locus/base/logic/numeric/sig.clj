(ns locus.base.logic.numeric.sig
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.numeric.ap :refer :all]))

; Let (N,+) be the set of natural numbers under addition. Then each natural number is associated to a set of additive
; partitions. These additive partitions can further be given the structure of a lattice to form Young's lattice:
; which is denoted (Y, join, meet). This is one of the fundamental lattice theoretic constructs that we are going
; to be working with so this file provides the basic foundations of Young's lattice theory. In particular, since
; Young's lattices is a distributive lattice we provide an implementation of a function that represents Young's
; lattice as a distributive lattice of sets.

; Conjugate partitions
(defn conjugate-partition
  [coll]

  (if (= (count coll) 0)
    (multiset '())
    (add
     (singleton-multiset (count coll))
     (conjugate-partition
      (multiset (filter (complement zero?) (map dec coll)))))))

; Block decomposition
(defn block-decomposition
  [sig]

  (letfn [(restricted-signature-cardinality [coll n]
            (count
             (filter
              (fn [i] (<= n i))
              coll)))]
    (let [conj (conjugate-partition sig)]
      (set
       (mapcat
        (fn [i]
          (let [maxj (restricted-signature-cardinality conj i)]
            (map
             (fn [j]
               (list i j))
             (range 1 (inc maxj)))))
        (range 1 (inc (count sig))))))))

(def signature-cardinality
  (comp count block-decomposition))

; Block recomposition
(defn get-maxy-block
  [coll]

  (let [max-yval (if (empty? coll)
               0
               (apply max (map second coll)))
        corresponding-max-xval (if (empty? coll)
                             0
                             (apply max (map first (filter (fn [[a b]] (= b max-yval)) coll))))]
    (list corresponding-max-xval max-yval)))

(defn remove-maxy-block
  [coll [max-xval max-yval]]

  (set
   (for [[x y] coll
         :let [current-xval (- x max-xval)]
         :when (and
                (not= y max-yval)
                (<= 1 current-xval))]
     [current-xval y])))

(defn block-recomposition
  [coll]

  (if (empty? coll)
    (multiset '())
    (let [[x y] (get-maxy-block coll)]
      (add
       (repeat-multiset x y)
       (block-recomposition (remove-maxy-block coll [x y]))))))

; Young's lattice operations
(defn young-join
  ([] (multiset '()))
  ([a] a)
  ([a b]
   (block-recomposition
    (union (block-decomposition a) (block-decomposition b))))
  ([a b & more]
   (reduce young-join (young-join a b) more)))

(defn young-meet
  ([a] a)
  ([a b]
   (block-recomposition
    (intersection (block-decomposition a) (block-decomposition b))))
  ([a b & more]
   (reduce young-meet (young-meet a b) more)))

; Young's lattice
(defn immediate-subpartitions
  [coll]

  (if (= (count coll) 0)
    #{}
    (set
      (for [i coll]
        (if (= i 1)
          (multiset-difference coll (singleton-multiset i))
          (add
            (singleton-multiset (dec i))
            (multiset-difference coll (singleton-multiset i))))))))

(defn all-subpartitions
  [coll]

  (if (= (count coll) 0)
    #{coll}
    (apply
     union
     (map
      (fn [i]
        (union #{coll} (all-subpartitions i)))
      (immediate-subpartitions coll)))))

(def covering-partition?
  (assoc (->Universal
          (fn [[a b]]
            (contains? (immediate-subpartitions b) a)))
         :arities #{2}))

(def superpartition?
  (assoc (->Universal
          (fn [[a b]]
            (contains? (all-subpartitions b) a)))
         :arities #{2}
         :join young-join
         :meet young-meet))
