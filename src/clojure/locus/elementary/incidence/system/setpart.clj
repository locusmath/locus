(ns locus.elementary.incidence.system.setpart
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all])
  (:import [locus.elementary.logic.base.core Universal SeqableUniversal]))

; Let Sets be the topos of sets. Then Sets is naturally associated with a congruence
; lattice for each object, which in this case simply reduces to the lattice of
; partitions of the set. This file handles such set partitions, their special
; forms, and their enumeration in each case.

; Functions for computing the cardinalities of partition lattices
(defn stirling2
  [n k]

  (*
   (/ (factorial k))
   (apply
    +
    (map
     (fn [i]
       (* (if (even? i) 1N -1N)
          (binomial-coefficient k i)
          (.pow (BigInteger/valueOf (- k i)) n)))
     (range (inc k))))))

(defn bell-number
  [n]

  (apply
   +
   (map
    (fn [i]
      (stirling2 n i))
    (range 1 (inc n)))))

; The number of edges in the partition lattice
(defn partition-ordering-count
  [n]

  (apply
   +
   (map
    (fn [k]
      (* (bell-number k)
         (stirling2 n k)))
    (range 1 (inc n)))))

(defn partition-covering-count
  [n]

  (/ (+ (bell-number n)
        (- (* 3 (bell-number (inc n))))
        (bell-number (+ n 2)))
     2))

; Enumeration of set partitions
; Starting by the enumeration of set partitions by their cardinality
; which is the only property intrinsic to them. 
(defn enumerate-set-partitions
  [coll]

  (cond
    (= (count coll) 0) '(#{})
    (= (count coll) 1) (list #{coll})
    :else (let [removable-parts (disj (power-set coll) #{})]
            (distinct
             (mapcat
              (fn [i]
                (let [partitions (enumerate-set-partitions
                                  (difference coll i))]
                  (map
                   (fn [partition]
                     (conj partition i))
                   partitions)))
              removable-parts)))))

(defn set-partitions
  [coll]

  (SeqableUniversal.
   (fn [partition]
     (and
      (universal? partition)
      (every? universal? partition)
      (every?
       (fn [pair]
         (empty? (apply intersection pair)))
       (selections partition 2))
      (= coll (apply union partition))))
   (enumerate-set-partitions coll)
   {:count (bell-number (count coll))}))

(defn enumerate-restricted-set-partitions
  [coll n]

  
  (cond
    (and (empty? coll) (= n 0)) '(#{})
    (empty? coll) '()
    (= n 1) (list #{coll})
    :else (distinct
           (mapcat
            (fn [i]
              (map
               (fn [partition]
                 (conj partition i))
               (enumerate-restricted-set-partitions (difference coll i) (dec n))))
            (disj (disj (power-set coll) #{}) coll)))))

(defn restricted-set-partitions
  [coll n]

  (SeqableUniversal.
   (fn [partition]
     (and
      (universal? partition)
      (every? universal? partition)
      (every?
       (fn [pair]
         (empty? (apply intersection pair)))
       (selections partition 2))
      (= (count partition) n)
      (= coll (apply union partition))))
   (enumerate-restricted-set-partitions coll n)
   {:count (stirling2 (count coll) n)}))

; Special types of restricted partitions
(defn pair-partitions
  [coll]

  (set
   (map
    (fn [i]
      #{i (difference coll i)})
    (disj (disj (power-set coll) #{}) coll))))

(defn atomic-set-partitions
  [coll]

  (set
   (map
    (fn [pair]
      (union #{pair}
             (set (map (fn [i] #{i}) (difference coll pair)))))
    (selections coll 2))))

; Ontology of set partitions by their members. With this we can classify
; set partitions by their member cardinalites rather then by their
; cardinality themselves.
(defn number-of-set-divisions
  ([n]

   (apply + (map
             (fn [i]
               (number-of-set-divisions n i))
             (divisors n))))
  ([n k]

   (if (not (divides? (list k n)))
     0
     (/ (factorial n)
        (let [d (/ n k)]
          (* (Math/pow (factorial k) d)
             (factorial d)))))))

(defn set-divisions
  "this does not return a set"
  ([coll]
   (mapcat
    (fn [i]
      (set-divisions coll i))
    (divisors (count coll))))
  ([coll n]

   (if (empty? coll)
     '(#{})
     (let [x (first coll)]
       (mapcat
        (fn [partial-selection]
          (let [selection (conj partial-selection x)]
            (map
             (fn [division]
               (conj division selection))
             (set-divisions (difference coll selection) n))))
        (selections (disj coll x) (dec n)))))))

; Set partitions by signatures
(defn signature-set-partition-count
  [sig]

  (let [sum (apply + sig)]
    (/ (factorial sum)
       (apply * (map
                 (fn [i]
                   (let [mult (multiplicity sig i)]
                     (* (factorial mult)
                        (Math/pow (factorial i) mult))))
                 (support sig))))))

(defn signature-set-partitions
  [coll sig]

  (let [current-size (apply + sig)]
    (cond
      (and (empty? coll) (empty? sig)) '(#{})
      (not= (count coll) current-size) '()
      (= current-size 1) (list #{#{(first coll)}})
      :else (let [block-member-size (apply max sig)
                  block-member-count (multiplicity sig block-member-size)
                  block-size (* block-member-size
                                block-member-count)]
              (mapcat
               (fn [selection]
                 (let [selection-divisions (set (set-divisions selection block-member-size))
                       remaining-partitions (set
                                             (signature-set-partitions
                                              (difference coll selection)
                                              (completely-remove-multiset-element sig block-member-size)))]
                   (map
                    (fn [[division partition]]
                      (union division partition))
                    (cartesian-product selection-divisions remaining-partitions))))
               (selections coll block-size))))))

; Set partition refinements and coarsifications
; The foundation of the ordering of the lattice of set partitions.
(defn set-partition-refinements
  [coll]

  (letfn [(product-of-finite-sets [& colls]
            (if (empty? colls)
              #{(list)}
              (set
               (mapcat
                (fn [i]
                  (map
                   #(cons i %)
                   (apply product-of-finite-sets (rest colls))))
                (first colls)))))]
    (set
     (map
      (partial apply union)
      (apply
       product-of-finite-sets
       (map enumerate-set-partitions coll))))))

(defn set-partition-coarsifications
  [partition]

  (set
   (map
    (fn [nested-partition]
      (set (map (partial apply union) nested-partition)))
    (enumerate-set-partitions partition))))

(defn direct-set-partition-coarsifications
  [partition]

  (if (<= (count partition) 1)
    #{}
    (set
     (map
      (fn [pair]
        (conj (difference partition pair) (apply union pair)))
      (selections partition 2)))))

(defn direct-set-partition-refinements
  [partition]

  (set
   (mapcat
    (fn [i]
      (map
       (fn [pair-partition]
         (union (disj partition i) pair-partition))
       (pair-partitions i)))
    partition)))

; Create a set partition by a function
(defn set-partition-by
  [func coll]

  (pn (fn [a b] (= (func a) (func b))) coll))

; Projections of partitions
(defn partition->projection
  [partition]

  (let [coll (apply union partition)
        sorted-partition (vec (seq partition))]
    (apply
      merge
      (map-indexed
        (fn [i v]
          (into
            {}
            (map
              (fn [j]
                [j i])
              v)))
        sorted-partition))))

(defn projection
  [partition dimember]

  (first
   (filter
    (fn [part]
      (part dimember))
    partition)))

; Restriction of partitions
(defn restrict-partition
  [partition coll]

  (set
   (for [i partition
         :let [current-intersection (intersection i coll)]
         :when (not (empty? current-intersection))]
     current-intersection)))

; We need some function to fix the issue of set partitions
; this turns a set system into a pairwise disjoint family.
(defn partitionize-family
  [coll]

  (loop [disjoint-elements #{}
         remaining-elements coll]
    (if (empty? remaining-elements)
      disjoint-elements
      (let [current-element (first remaining-elements)
            intersecting-elements (set
                                   (filter
                                    (fn [i]
                                      (not (empty? (intersection i current-element))))
                                    remaining-elements))
            isdisjoint (<= (count intersecting-elements) 1)]
        (recur
         (if isdisjoint
           (conj disjoint-elements current-element)
           disjoint-elements)
         (if isdisjoint
           (disj remaining-elements current-element)
           (conj (difference remaining-elements intersecting-elements)
                 (apply union intersecting-elements))))))))

; Lattice operations
(def join-set-partitions
  (fn
    ([a] a)
    ([a b] (partitionize-family (union a b)))
    ([a b & more] (reduce join-set-partitions (join-set-partitions a b) more))))

(def meet-set-partitions
  (fn
    ([a] a)
    ([a b]
     (apply
       union
       (map
         (fn [i]
           (restrict-partition b i))
         a)))
    ([a b & more]
     (reduce meet-set-partitions (meet-set-partitions a b) more))))

(def set-superpartition?
  (assoc (Universal.
          (intersection
           seq?
           (fn [[a b]]
             (= (join-set-partitions a b) b))))
         :arities #{2}
         :join (fn [& args]
                 (apply join-set-partitions args))
         :meet (fn [& args]
                 (apply meet-set-partitions args))))

; Partition product and coproduct
(defn partition-product
  [& partitions]

  (set
   (map
    (fn [coll]
      (apply cartesian-product coll))
    (apply cartesian-product partitions))))

(defn partition-coproduct
  [& partitions]

  (apply
   union
   (map-indexed
    (fn [i partition]
      (set
       (map
        (fn [part]
          (set
           (map
            (fn [elem]
              (list i elem))
            part)))
        partition)))
    partitions)))

