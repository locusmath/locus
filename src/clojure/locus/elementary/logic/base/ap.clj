(ns locus.elementary.logic.base.ap
  (:require [locus.elementary.logic.base.core :refer :all]))

; Let (N,+) be the set of natural numbers equipped with addition. Then every natural number is
; associated to a set of additive partitions of it. These can be classified further based upon
; the properties of the additive partition, such as the number of parts and the maximum
; and minimum values available in it. This file deals with the enumeration of these additive
; partitions subject to a variety of different constraints.

; Enumeration of all additive partitions 
(defn restricted-partitions
  "This lists the additive partitions of n into k parts."
  [n k]
  (cond
   (= n k 0) '(())
   (or (<= k 0) (< n k)) '()
   (= k 1) (list (list n))
   (= n (inc k)) (list (concat (repeat (dec k) 1) (list 2)))
   (= n k) (list (repeat n 1))
   :else (mapcat
          (fn [i]
            (map
             (fn [coll]
               (cons
                i
                (map #(+ % (dec i)) coll)))
             (restricted-partitions (- n i (* (dec k) (dec i)))
                (dec k))))
          (range 1 (inc n)))))

(defn all-partitions
  [n]

  (if (zero? n)
    #{(multiset '())}
    (set
     (mapcat
      (fn [i]
        (map multiset (restricted-partitions n i)))
      (range 1 (inc n))))))

(defn partitions-upto
  [n]
  
  (apply
   union
   (map
    (fn [i]
      (all-partitions i))
    (range (inc n)))))

; Enumeration of additive partitions by their multiset signatures
; this includes equal and distinct additive partitions as special
; cases that have signatures of ones or of size one. Unlike sumsets
; these do not make reference to the elements of the partition.
(defn minimum-positive-integers
  [num forbidden-numbers]

  (if (empty? forbidden-numbers)
    (range 1 (inc num))
    (let [forbidden-maximum (apply max forbidden-numbers)
          enclosed-count (- forbidden-maximum (count forbidden-numbers))
          enclosed-elements (take
                             (min num enclosed-count)
                             (for [i (range 1 forbidden-maximum)
                                   :when (not (contains? forbidden-numbers i))]
                               i))]
      (if (<= num enclosed-count)
        enclosed-elements
        (concat
         enclosed-elements
         (range
          (inc forbidden-maximum)
          (+ (inc forbidden-maximum) (- num enclosed-count))))))))

(defn minimum-signature-sum
  [sorted-signature forbidden-numbers]

  (let [minimum-integers (minimum-positive-integers
                          (apply + sorted-signature)
                          forbidden-numbers)]
    (apply +
           (map
            (fn [i]
              (* (nth sorted-signature i)
                 (nth minimum-integers i)))
            (range (count sorted-signature))))))

(defn signature-partitions
  ([num signature] (signature-partitions num (vec (sort > (seq signature))) #{}))
  ([num signature forbidden-numbers]

   (if (empty? signature)
     (if (= num 0)
       '(#{})
       '())
     (let [signature-maximum (first signature)
           remaining-signature (rest signature)]
       (if (< num (minimum-signature-sum signature forbidden-numbers))
         '()
         (if (= num 0)
           '(#{})
           (mapcat
            (fn [i]
              (if (contains? forbidden-numbers i)
                '()
                (let [remaining-partitions (signature-partitions
                                            (- num (* signature-maximum i))
                                            remaining-signature
                                            (conj forbidden-numbers i))]
                  (map
                   (fn [partition]
                     (add partition (repeat-multiset signature-maximum i)))
                   remaining-partitions))))
            (range 1 (inc (inc (/ num signature-maximum)))))))))))

; Enumeration of equal additive partitions
(defn restricted-additive-divisions
  [n k]

  (if (divides? (list k n))
    #{(repeat-multiset k (int (/ n k)))}
    #{}))

(defn number-of-divisors
  [n]

  (count (divisors n)))

(defn additive-divisions
  [n]

  (set
   (map
    (fn [d]
      (let [q (int (/ n d))]
        (repeat-multiset q d)))
    (divisors n))))

; Enumeration of distinct additive partitions
(defn restricted-distinct-partitions
  [n k]

  (set (signature-partitions n (repeat-multiset k 1))))

(defn distinct-partitions
  [n minval]

  (if (zero? n)
    #{(multiset '())}
    (if (< n minval)
      #{}
      (let [remaining-partitions (set
                                  (map
                                   (fn [partition]
                                     (add partition (singleton-multiset minval)))
                                   (distinct-partitions (- n minval) (inc minval))))
            higher-minimum-partitions (distinct-partitions n (inc minval))]
        (union
         remaining-partitions
         higher-minimum-partitions)))))

(defn all-distinct-partitions
  [n]

  (distinct-partitions n 1))

; Additive partitions of numbers into kuratowski pair multisets
(defn kuratowski-additive-partitions
  [n]

  (set (signature-partitions n (multiset '(1 2)))))

; Additive partitions by restricted sets of elements 
; These are additive partitions that are restricted by their members
; rather then by their properties as partitions in and of themselves.
(defn interval-partitions
  [n minval maxval]

  (if (zero? n)
    #{(multiset '())}
    (if (or (< n minval)
            (< maxval minval)
            (neg? n))
      #{}
      (union
       (set
        (map
         (fn [partition]
           (add partition (singleton-multiset minval)))
         (interval-partitions (- n minval) minval maxval)))
       (interval-partitions n (inc minval) maxval)))))

(defn min-partitions
  [n minval]

  (if (zero? n)
    #{(multiset '())}
    (if (or (neg? n) (< n minval))
      #{}
      (union
       (set
        (map
         (fn [partition]
           (add partition (singleton-multiset minval)))
         (min-partitions (- n minval) minval)))
       (min-partitions n (inc minval))))))

(defn max-partitions
  [n maxval]

  (interval-partitions n 1 maxval))

; One two partitions are merely a very simple special case 
; that demonstrates the use of sumsets
(defn one-two-partitions
  [n]

  (let [max2 (int (/ n 2))]
    (set
     (map
      (fn [two-count]
        (let [one-count (- n (* 2 two-count))]
          (add (repeat-multiset one-count 1)
               (repeat-multiset two-count 2))))
      (range (inc max2))))))

; Sumsets can be dealt with by determining all additive partitions
; of numbers whose components belong to a given set
(defn partitions-by-set
  [n coll]

  (let [current-min (if (empty? coll)
                      0
                      (apply min coll))]
    (cond
      (zero? n) #{#{}}
      (empty? coll) #{}
      (neg? n) #{}
      :else (union
             (set
              (map
               (fn [partition]
                 (add partition (singleton-multiset current-min)))
               (partitions-by-set (- n current-min) coll)))             
             (partitions-by-set n (disj coll current-min))))))

(defn in-unrestricted-sumset?
  [n coll]

  (not (empty? (partitions-by-set n coll))))

(defn unrestricted-sumset
  [coll]

  (fn [n]
    (not (empty? (partitions-by-set n coll)))))






