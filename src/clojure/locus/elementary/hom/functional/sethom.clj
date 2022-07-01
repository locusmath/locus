(ns locus.elementary.hom.functional.sethom
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all])
  (:import [locus.elementary.logic.base.core SeqableUniversal]
           [locus.elementary.function.core.object SetFunction]))

; This file supports the enumeration of hom classes in the topos of Sets.
; These consist of various classes of functions between two sets, and in particular
; specialized hom classes consisting of epi, mono, and isomorphisms of sets.

; Enumeration theory of the topos of sets
(defn number-of-mappings
  [a b]

  (.pow (BigInteger/valueOf (count b)) (count a)))

(defn enumerate-mappings
  [a b]

  (map
   (fn [coll] (zipmap a coll))
   (seqable-cartesian-power b (count a))))

(defn enumerate-self-mappings
  [coll]

  (enumerate-mappings coll coll))

(defn seqable-mappings
  [a b]

  (SeqableUniversal.
    (fn [i]
      (and
        (map? i)
        (every? a (keys i))
        (every? b (vals i))))
    (enumerate-mappings a b)
    {:count (number-of-mappings a b)}))

(defn enumerate-partial-mappings
  [a b]

  (map
    (fn [coll]
      (apply
        merge
        (map-indexed
          (fn [i v]
            (if (zero? v)
              {}
              {(nth a i) (nth b (dec v))}))
          coll)))
    (seqable-cartesian-power (set (range (inc (count b)))) (count a))))

(defn seqable-partial-mappings
  [a b]

  (SeqableUniversal.
    (fn [i]
      (and
        (map? i)
        (every? a (keys i))
        (every? b (vals i))))
    (enumerate-partial-mappings (vec a) (vec b))
    {:count (.pow (BigInteger/valueOf (inc (count b))) (count a))}))

(defn set-hom
  [a b]

  (SeqableUniversal.
   (fn [i]
     (and
      (set-function? i)
      (in-hom-class? i a b)))
   (map #(SetFunction. a b %) (enumerate-mappings a b))
   {:count (number-of-mappings a b)}))

; Enumerate injections
(defn falling-cartesian-product
  [n k]

  (apply
   seqable-cartesian-product
   (map
    (fn [i] (set (range (- n i))))
    (range k))))

(defn convert
  [indices n]

  (loop [i 0
         possible-selections (set (range n))
         rval '()]
    (if (= i (count indices))
      rval
      (let [current-index (nth indices i)
            sorted-selection (sort < (seq possible-selections))
            current-selection (nth sorted-selection current-index)]
        (recur
         (inc i)
         (disj possible-selections current-selection)
         (concat rval (list current-selection)))))))

(defn all-permutations
  [n]

  (SeqableUniversal.
   (fn [coll]
     (and
      (distinct-seq? coll)
      (every? (fn [i] (int? i) (<= 0 i (dec n))) coll)))
   (map
    #(convert % n)
    (falling-cartesian-product n n))
   {}))

; Injective set hom
(defn number-of-injections
  [a b]

  (falling-factorial (count b) (count a)))

(defn enumerate-injective-mappings
  [a b]

  
  (let [sorted-inputs (seq a)
        sorted-outputs (seq b)]
    (map
     (fn [i]
       (let [indices (convert i (count b))
             mapping (zipmap
                      sorted-inputs
                      (map (fn [i] (nth sorted-outputs i)) indices))]
         mapping))
     (falling-cartesian-product (count b) (count a)))))

(defn injective-set-hom
  [a b]

  (SeqableUniversal.
   (fn [i]
     (and
      (injective? i)
      (in-hom-class? i a b)))
   (map
    #(SetFunction. a b %)
    (enumerate-injective-mappings a b))
   {:count (number-of-injections a b)}))

(defn enumerate-permutation-maps
  [arg]

  (let [coll (if (vector? arg) arg (seq arg))]
    (map
      (fn [i]
        (zipmap coll i))
      (enumerate-sequence-permutations coll))))

(defn bijective-set-hom
  [a b]

  (if (= (count a) (count b))
    (injective-set-hom a b)
    #{}))

; Surjection enumeration
(defn number-of-surjections
  [a b]

  (* (factorial (count b)) (stirling2 (count a) (count b))))

(defn surjective-set-hom
  [a b]

  (SeqableUniversal.
   (fn [i]
     (and
      (surjective? i)
      (in-hom-class? i a b)))
   (let [sorted-outputs (seq b)]
     (map
      (fn [[partition perm]]
        (let [len (count perm)
              ordered-partition (seq partition)
              permuted-partition (map
                                  (fn [i]
                                    (nth ordered-partition (nth perm i)))
                                  (range len))]
          (SetFunction.
           a
           b
           (apply
            merge
            (map
             (fn [i]
               (zipmap
                (nth permuted-partition i)
                (repeat (count (nth permuted-partition i))
                        (nth sorted-outputs i))))
             (range len))))))
      (cartesian-product
       (restricted-set-partitions a (count b))
       (all-permutations (count b)))))
   {:count (number-of-surjections a b)}))




