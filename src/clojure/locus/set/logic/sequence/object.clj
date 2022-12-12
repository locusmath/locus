(ns locus.set.logic.sequence.object
  (:require [clojure.set]
            [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all])
  (:import [locus.set.logic.core.set Universal SeqableUniversal]))

; Order indexed functions
; Lists are order indexed functions which is why they do not have a
; lattice based ordering like most foundational data structures. Ordinal
; indexed functions are necessarily associated with two types
; of additional structures: the indices partition of inputs
; and the multiset of outputs.

; We need some support for permutations of sequences
; The input to this should be a set rather then an ordinary sequence
(defn enumerate-permutations
  [coll]

  (if (empty? coll)
    #{(list)}
    (let [sorted-coll (seq coll)]
      (apply
        union
        (map
          (fn [i]
            (set
              (map
                (partial cons i)
                (enumerate-permutations
                  (clojure.set/difference coll #{i})))))
          coll)))))

(defn enumerate-sequence-permutations
  [coll]

  (set
    (map
      (fn [perm]
        (map (partial nth coll) perm))
      (enumerate-permutations (set (range (count coll)))))))

; Composition on the level of sequences
(defn compose-sequences
  ([a b] (compose-sequences a b (count b)))
  ([a b n]
   (map
     (fn [i]
       (nth a (nth b i)))
     (range n))))

(defn compose-vectors
  ([a b] (compose-vectors a b (count b)))
  ([a b n] (vec (compose-sequences a b n))))

; Convert between vectors and maps
(defn vector->map
  [coll]

  (into {} (map-indexed (fn [i v] [i v]) coll)))

(defn map->vector
  [coll]

  (vec (map (fn [i] (get coll i)) (range (count coll)))))

; Indices partitions
(defn indices
  [coll]

  (set (range (count coll))))

(defn indices-partition
  [coll]

  (let [distinct-elems (set coll)]
    (set
      (map
        (fn [elem]
          (set
            (filter
              (fn [i]
                (= (nth coll i) elem))
              (range (count coll)))))
        distinct-elems))))

(defn classified-indices-partition
  [coll]

  (comp (partial = coll) indices-partition))

; Restrict a list to a simplified set of indices
(defn restrict-list
  [coll indices]

  (map
    (fn [i]
      (nth coll i))
    (sort < indices)))

; Classes of sequences as determined by their
; multiplicities multisets
(def equal-seq?
  (intersection
    seq?
    (fn [i]
      (<= (count (set i)) 1))))

(def distinct-seq?
  (fn [coll]
    (and
      (seq? coll)
      (= (count coll) (count (set coll))))))

(def unique-seq?
  (assoc (Universal.
           (fn [coll]
             (and
               (seq? coll)
               (<= (count coll) 1))))
    :arities #{0 1}))

(def singular-seq?
  (assoc (Universal.
           (cartesian-power entity? 1))
    :arities #{1}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [0 0] entity?
               #{}))))

(def max-size-two-seq?
  (assoc (Universal.
           (fn [coll]
             (and
               (seq? coll)
               (<= (count coll) 2))))
    :arities #{0 1 2}))

(def size-two-seq?
  (assoc (Universal.
           (cartesian-power entity? 2))
    :arities #{2}))

(def distinct-size-two-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0} #{1}}))
    :arities #{2}))

(def equal-size-two-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0 1}}))
    :arities #{2}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[x] []] arg] #{x})
               [0 1] (let [[[] [y]] arg] #{y})
               #{}))))

(def max-size-three-seq?
  (assoc (Universal.
           (fn [coll]
             (and
               (seq? coll)
               (<= (count coll) 2))))
    :arities #{0 1 2 3}))

(def size-three-seq?
  (assoc (Universal.
           (cartesian-power entity? 3))
    :arities #{3}))

(def distinct-size-three-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0} #{1} #{2}}))
    :arities #{3}))

(def equal-size-three-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0 1 2}}))
    :arities #{3}))

(def max-size-four-seq?
  (assoc (Universal.
           (fn [coll]
             (and
               (seq? coll)
               (<= (count coll) 2))))
    :arities #{0 1 2 3 4}))

(def size-four-seq?
  (assoc (Universal.
           (cartesian-power entity? 4))
    :arities #{4}))

(def distinct-size-four-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0} #{1} #{2} #{3}}))
    :arities #{4}))

(def equal-size-four-seq?
  (assoc (Universal.
           (classified-indices-partition #{#{0 1 2 3}}))
    :arities #{4}))

; The two main properties of sequences are the indices partition
; and the underlying multiset as previously described. The
; intersection of these two properties is the signature.
(defn !=seq
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= a b)))

(defn !=underlying-multiset
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (multiset a) (multiset b))))

(defn !=indices-partition
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (indices-partition a) (indices-partition b))))

(defn !=sequence-signature
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (signature (multiset a)) (signature (multiset b)))))

; Other properties of the sequence
(defn !=sequence-support
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (set a) (set b))))

(defn !=sequence-size
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (count a) (count b))))

(defn !=sequence-order
  [a b]

  (and
    (seq? a)
    (seq? b)
    (not= (count (set a)) (count (set b)))))

; Pairs
(defn !=pair
  [a b]

  (and
    (size-two-seq? a)
    (size-two-seq? b)
    (not= a b)))

(defn !=pair-first
  [a b]

  (and
    (size-two-seq? a)
    (size-two-seq? b)
    (not= (first a) (first b))))

(defn !=pair-second
  [a b]

  (and
    (size-two-seq? a)
    (size-two-seq? b)
    (not= (second a) (second b))))

; Triples
(defn !=triple
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (not= a b)))

(defn !=triple-first
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (not= (first a) (first b))))

(defn !=triple-second
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (not= (second a) (second b))))

(defn !=triple-third
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (not= (nth a 2) (nth b 2))))

(defn !=triple-front
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (or
      (not= (first a) (first b))
      (not= (second a) (second b)))))

(defn !=triple-outside
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (or
      (not= (first a) (first b))
      (not= (nth a 2) (nth b 2)))))

(defn !=triple-back
  [a b]

  (and
    (size-three-seq? a)
    (size-three-seq? b)
    (or
      (not= (second a) (second b))
      (not= (nth a 2) (nth b 2)))))

; Quadruples
(defn !=quadruple
  [a b]

  (and
    (size-four-seq? a)
    (size-four-seq? b)
    (not= a b)))

; Index reductions
(defn index-reductions
  [coll]

  (set
    (map
      (fn [indices]
        (map (partial nth coll) (sort < indices)))
      (power-set (set (range (count coll)))))))

(def index-promotion?
  (assoc (Universal.
           (fn [[a b]]
             (or
               (empty? a)
               (let [current-first (first a)
                     contains-first? (not
                                       (empty?
                                         (filter
                                           (partial = current-first)
                                           b)))]
                 (and
                   contains-first?
                   (let [current-index (first
                                         (filter
                                           (fn [i]
                                             (= (nth b i) current-first))
                                           (range (count b))))]
                     (index-promotion? (list (rest a) (drop (inc current-index) b)))))))))
    :arities #{2}
    :query (fn [arg]
             (case [(count (first arg)) (count (second arg))]
               [1 0] (let [[[a] []] arg]
                       (fn [i]
                         (index-promotion? (list a i))))
               [0 1] (let [[[] [b]] arg]
                       (index-reductions b))
               #{}))))

; Consecutive supersequences
(def supersequence?
  (letfn [(consecutive-sublists [coll]
            (set
              (for [indices (power-set (set (range (count coll))))
                    :when (every?
                            (fn [i]
                              (or
                                (contains? indices (inc i))
                                (= i (apply max indices))))
                            indices)]
                (map (partial nth coll) (sort < indices)))))
          (superlist-relation [[a b]]
            (and
              (<= (count a) (count b))
              (not
                (every?
                  (complement
                    (fn [start-index]
                      (= a
                         (map
                           (partial nth b)
                           (range start-index (+ start-index (count a)))))))
                  (range (inc (- (count b) (count a))))))))]
    (assoc (Universal. superlist-relation)
      :arities #{2}
      :query (fn [arg]
               (case [(count (first arg)) (count (second arg))]
                 [1 0] (let [[[a] []] arg]
                         (fn [i]
                           (superlist-relation (list a i))))
                 [0 1] (let [[[] [b]] arg]
                         (consecutive-sublists b))
                 #{})))))

(def prefix-supersequence?
  (letfn [(sublists [b]
            (set
              (map
                (fn [i]
                  (take i b))
                (range (inc (count b))))))
          (superlist-relation [[a b]]
            (= a (take (count a) b)))]
    (assoc (Universal. superlist-relation)
      :arities #{2}
      :query (fn [arg]
               (case [(count (first arg)) (count (second arg))]
                 [1 0] (let [[[a] []] arg]
                         (fn [i]
                           (superlist-relation (list a i))))
                 [0 1] (let [[[] [b]] arg]
                         (sublists b))
                 #{})))))

(def suffix-supersequence?
  (letfn [(sublists [b]
            (set
              (map
                (fn [i]
                  (nthrest b i))
                (range (inc (count b))))))
          (superlist-relation [[a b]]
            (= a (nthrest b (- (count b) (count a)))))]
    (assoc (Universal. superlist-relation)
      :arities #{2}
      :query (fn [arg]
               (case [(count (first arg)) (count (second arg))]
                 [1 0] (let [[[a] []] arg]
                         (fn [i]
                           (superlist-relation (list a i))))
                 [0 1] (let [[[] [b]] arg]
                         (sublists b))
                 #{})))))