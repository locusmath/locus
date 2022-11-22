(ns locus.elementary.relation.binary.sr
  (:require [clojure.set]
            [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all])
  (:import [locus.base.logic.core.set Universal SeqableUniversal]
           [locus.elementary.relation.binary.product CompleteRelation BinaryCartesianProduct]))

; The purpose of this file is to provide support for the implementation of special paramaterized
; families of binary relations. We have tried to make our implementation as lazy as possible
; in order to improve performance. Ideally, a binary relation should be implemented as predicate
; with the actual sequence of elements produced on demand.

; Implementation of seqable relations
(deftype SeqableRelation [vertices pred attrs]
  clojure.lang.Seqable
  (seq [this]
    (let [coll (filter pred (cartesian-power vertices 2))]
      (if (empty? coll)
        nil
        coll)))

  clojure.lang.Counted
  (count [this]
    (if (not (nil? (:count attrs)))
      (min Integer/MAX_VALUE (:count attrs))
      (count (seq this))))

  clojure.lang.IFn
  (invoke [this obj]
    (pred obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SeqableRelation :locus.base.logic.core.set/universal)

(defmethod vertices SeqableRelation
  [rel]

  (.vertices rel))

(defn relation-order
  [rel]

  (count (vertices rel)))

; Seqable binary relation
(defn seqable-binary-relation
  [source target pred]

  (seqable-filter pred (->BinaryCartesianProduct source target)))

; Fundamental constructs in the theory of relations
(defn product-relation
  [& relations]

  (SeqableRelation.
    (apply cartesian-product (map vertices relations))
    (fn [[coll1 coll2]]
      (every?
        (fn [i]
          ((nth relations i)
           (list (nth coll1 i)
                 (nth coll2 i))))
        (range (count relations))))
    {:count (apply * (map count relations))}))

(defn sum-relation
  [& relations]

  (SeqableRelation.
    (apply cartesian-coproduct (map vertices relations))
    (fn [[[i x] [j y]]]
      (and
        (= i j)
        ((nth relations i) (list x y))))
    {:count (apply + (map count relations))}))

; Take a set system and gets corresponding inclusion partial ordering
(defn family-inclusion-ordering
  [coll]

  (SeqableRelation.
    coll
    (fn [[i j]]
      (superset? (list i j)))
    {}))

; Complete relations
(defn complete-relation
  [coll]

  (CompleteRelation. coll))

(defn equivalence-relation
  [partition]

  (let [coll (apply union partition)]
    (SeqableRelation.
      coll
      (fn [[a b]]
        (not
          (every?
            (fn [part]
              (not
                (and
                  (contains? part a)
                  (contains? part b))))
            partition)))
      {:count (apply + (map (comp (fn [n] (* n n)) count) partition))})))

(defn coreflexive-relation
  [coll]

  (SeqableRelation.
    coll
    (fn [[a b]]
      (= a b))
    {:count (count coll)}))

; The reason that a power of three is used in the power set ordering
; is that ordered pairs of sets classify elements into three 
; different types of relations.
(defn power-set-ordering
  [coll]

  (SeqableRelation.
    (seqable-power-set coll)
    (fn [[a b]]
      (superset? (list a b)))
    {:count (power-of-three (count coll))}))

(defn power-set-restriction-ordering
  [coll]

  (SeqableRelation.
    (seqable-power-set coll)
    (fn [[a b]]
      (superset? (list b a)))
    {:count (power-of-three (count coll))}))

; We need a special function for counting the number of elements of the covering relation of
; a power set and its associated relation.
(defn number-of-hypercube-edges
  [n]

  (if (zero? n)
    0
    (* n (power-of-two (dec n)))))

(defn power-set-covering
  [coll]

  (SeqableRelation.
    (seqable-power-set coll)
    (fn [[a b]]
      (and
        (superset? (list a b))
        (= (count (difference b a)) 1)))
    {:count (number-of-hypercube-edges (count coll))}))

; The power set independence relation has essentially the same number of edges as the
; power set ordering relation because they are basically equivalent by differences.
(defn power-set-independence-relation
  [coll]

  (SeqableRelation.
    (seqable-power-set coll)
    (fn [[a b]]
      (empty? (intersection a b)))
    {:count (power-of-three (count coll))}))

; We can also form a power clan ordering by using the same basic
; principle of getting the product of triangular numbers
(defn triangular-number
  [n]

  (loop [rval 0N
         i 1]
    (if (< n i)
      rval
      (recur (+ rval i) (inc i)))))

(defn power-clan-ordering
  [coll]

  (SeqableRelation.
    (seqable-power-clan coll)
    (fn [[a b]]
      (superbag? (list a b)))
    {:count (apply * (map (comp triangular-number inc) (signature coll)))}))

; Define an inclusion relation
; This naturally are a generalisation of the inclusion relations of power sets
(defn inclusion-relation
  [family]

  (SeqableRelation.
    family
    (fn [pair]
      (superset? pair))
    {}))

; A seqable relations version of the ordinal sum is implemented so that
; we don't have to manually calculate the edge size of the resulting relation.
(defn ordinal-sum-cardinality
  [nums]

  (apply +
         (map
           (fn [i]
             (* (nth nums i) (apply + (nthrest nums (inc i)))))
           (range (count nums)))))

(defn ordinal-sum
  [& relations]

  (SeqableRelation.
    (apply cartesian-coproduct (map vertices relations))
    (fn [[[i x] [j y]]]
      (or
        (< i j)
        (and
          (= i j)
          ((nth relations i) (list x y)))))
    {:count (+ (apply + (map count relations))
               (ordinal-sum-cardinality (map relation-order relations)))}))

; The most basic types of ordering relation are total orders, weak
; orders and sets of lists.
(defn total-order
  "A total order on the set of arguments passed to this function."
  [& coll]

  (let [coll-vector (vec coll)
        coll-set (set coll)]
    (SeqableRelation.
      coll-set
      (fn [[a b]]
        (<= (.indexOf coll-vector a)
            (.indexOf coll-vector b)))
      {:count (triangular-number (count coll-set))})))

(defn set-of-lists
  "Each argument to this function should be a vector."
  [lists]

  (let [coll (apply union (map set lists))
        lists-vector (vec lists)
        sorted-coll (seq coll)
        positions-map (zipmap
                        sorted-coll
                        (map
                          (fn [val]
                            (first
                              (filter
                                (fn [i]
                                  (not= -1 (.indexOf (nth lists-vector i) val)))
                                (range (count lists-vector)))))
                          sorted-coll))]
    (SeqableRelation.
      coll
      (fn [[a b]]
        (and
          (= (positions-map a) (positions-map b))
          (let [current-coll (nth lists-vector (positions-map a))]
            (<= (.indexOf current-coll a)
                (.indexOf current-coll b)))))
      {:count (apply
                +
                (map (comp triangular-number count) lists))})))

(defn weak-order
  "A weak order of an ordered partition."
  [ordered-partition]

  (let [coll (apply union ordered-partition)
        positions-map (apply
                        merge
                        (map-indexed
                          (fn [i v]
                            (zipmap
                              (seq v)
                              (repeat (count v) i)))
                          ordered-partition))]
    (SeqableRelation.
      coll
      (fn [[a b]]
        (or
          (= a b)
          (< (positions-map a) (positions-map b))))
      {:count (let [ordered-composition (map count ordered-partition)]
                (+ (apply + ordered-composition)
                   (ordinal-sum-cardinality ordered-composition)))})))

(defn total-preorder
  "A total preorder of an ordered partition."
  [ordered-partition]

  (let [coll (apply union ordered-partition)
        positions-map (apply
                        merge
                        (map-indexed
                          (fn [i v]
                            (zipmap
                              (seq v)
                              (repeat (count v) i)))
                          ordered-partition))]
    (SeqableRelation.
      coll
      (fn [[a b]] (<= (positions-map a) (positions-map b)))
      {:count (let [ordered-composition (map count ordered-partition)]
                (+ (apply + (map (fn [n] (* n n)) ordered-composition))
                   (ordinal-sum-cardinality ordered-composition)))})))

; Create a weak preorder from an ordered sequence of set partitions
(defn weak-preorder
  [partitions]

  (apply ordinal-sum (map equivalence-relation partitions)))

; Partition statistics
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

; We have special support for partition ordering and covering relations
; this is fortunately supportable thanks to our partition ordering
; and covering count functions.
(defn partition-ordering
  [coll]

  (SeqableRelation.
    (set-partitions coll)
    (fn [[a b]]
      (set-superpartition? (list a b)))
    {:count (partition-ordering-count (count coll))}))

(defn partition-covering
  [coll]

  (SeqableRelation.
    (set-partitions coll)
    (fn [[a b]]
      (and
        (set-superpartition? (list a b))
        (= (inc (count b)) (count a))))
    {:count (partition-covering-count (count coll))}))

; The tamari lattice relation
; This has the very nice and convenient property that it has a well
; known combinatorial formula for the number of edges in it.
(defn tamari-bracketing-vector?
  [coll]

  (let [n (dec (count coll))]
    (and
      (every?
        (fn [i]
          (<= i (nth coll i) n))
        (range (count coll)))
      (every?
        (fn [[i j]]
          (or
            (not
              (<= i j (nth coll i)))
            (<= (nth coll j) (nth coll i))))
        (cartesian-power (set (range (count coll))) 2)))))

(defn tamari-bracketing-vectors
  [n]

  (filter
    tamari-bracketing-vector?
    (cartesian-power (set (range n)) n)))

(defn tamari-ordering-size
  [n]

  (/ (* 2 (factorial (inc (* 4 n))) )
     (* (factorial (inc n))
        (factorial (+ (* 3 n) 2)))))

(defn tamari-ordering
  [n]

  (SeqableRelation.
    (SeqableUniversal.
      tamari-bracketing-vector?
      (tamari-bracketing-vectors n)
      {})
    (fn [[a b]]
      (every?
        (fn [i]
          (<= (nth a i) (nth b i)))
        (range (min (count a) (count b)))))
    {:count (tamari-ordering-size n)}))

; Interval orderings
(defn is-interval-of?
  [n a b]

  (and
    (int? a)
    (int? b)
    (<= a b)
    (<= 0 a (dec n))
    (<= 0 b (dec n))))

(defn enumerate-proper-intervals
  [n]

  (if (zero? n)
    '()
    (mapcat
      (fn [i]
        (map
          (fn [j]
            [i j])
          (range i n)))
      (range n))))

(defn all-proper-intervals
  [n]

  (SeqableUniversal.
    (fn [[a b]] (is-interval-of? n a b))
    (enumerate-proper-intervals n)
    {:count (triangular-number n)}))

(defn enumerate-all-intervals
  [n]

  (cons [] (enumerate-proper-intervals n)))

(defn all-intervals
  [n]

  (SeqableUniversal.
    (fn [pair]
      (or
        (empty? pair)
        (and
          (coll? pair)
          (= (count pair) 2)
          (let [[a b] pair]
            (is-interval-of? n a b)))))
    (enumerate-all-intervals n)
    {:count (inc (triangular-number n))}))

(defn pentatope-number
  [n]

  (binomial-coefficient (+ n 3) 4))

(defn intervals-containment-ordering
  [n]

  (if (zero? n)
    #{}
    (SeqableRelation.
      (all-proper-intervals n)
      (fn [[[l1 u1] [l2 u2]]]
        (and (<= u1 u2)
             (<= l2 l1)))
      {:count (pentatope-number n)})))

(defn intervals-containment-covering
  [n]

  (if (zero? n)
    #{}
    (SeqableRelation.
      (all-proper-intervals n)
      (fn [[[l1 u1] [l2 u2]]]
        (or (and (= l1 l2)
                 (= (inc u1) u2))
            (and (= u1 u2)
                 (= (inc l2) l1))))
      {:count (cond
                (zero? n) 0
                (= n 1) 1
                :else (* n (dec n)))})))

; Join and meet precedence relations determined by functions
(defn join-precedence-relation
  [coll join]

  (SeqableRelation.
    coll
    (fn [[a b]]
      (= (join a b) b))
    {}))

(defn meet-precedence-relation
  [coll meet]

  (SeqableRelation.
    coll
    (fn [[a b]]
      (= (meet a b) a))
    {}))
