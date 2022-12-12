(ns locus.con.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [dorothy.core :as dot]))

; Ontology of set partitions
(derive ::set-partition :locus.set.logic.structure.protocols/structured-set)
(derive ::relational-partition ::set-partition)
(derive ::functional-partition ::relational-partition)
(derive ::familial-partition ::set-partition)

; Multimethods for dealing with set partitions
(defmulti equivalence-classes type)

(defmulti equal? (fn [p a b] (type p)))

(defn different?
  [p a b]

  (not (equal? p a b)))

; The number of equivalence classes of a set partition
(defn number-of-equivalence-classes
  [partition]

  (count (equivalence-classes partition)))

; Underlying relations
(defn equivalence-relation
  [partition]

  (apply
    union
    (set
      (map
        (fn [i]
          (cartesian-product i i))
        partition))))

(defmethod underlying-relation ::set-partition
  [partition]

  (equivalence-relation (equivalence-classes partition)))

(defmethod underlying-multirelation ::set-partition
  [partition]

  (underlying-relation partition))

; Projection functions
(defn projection
  [partition dimember]

  (first
    (filter
      (fn [part]
        (part dimember))
      partition)))

(defn restrict-partition
  [partition coll]

  (set
    (for [i partition
          :let [current-intersection (intersection i coll)]
          :when (not (empty? current-intersection))]
      current-intersection)))

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

; Equivalence class of
(defmulti equivalence-class-of (fn [p a] (type p)))

(defmethod equivalence-class-of ::set-partition
  [partition coll]

  (projection (equivalence-classes partition) coll))

; Set partitions
; A set partition can be represented by the explicit presentation of all the equivalence classes
; of an equivalence relation.
(deftype SetPartition [partition]
  ConcreteObject
  (underlying-set [this]
    (apply union partition)))

(derive SetPartition ::set-partition)

(defmethod equivalence-class-of SetPartition
  [^SetPartition p, x]

  (projection (.-partition p) x))

(defmethod equivalence-classes SetPartition
  [^SetPartition partition] (.-partition partition))

(defmethod equal? SetPartition
  [^SetPartition set-partition, a, b]

  (boolean ((projection (.-partition set-partition) a) b)))

(defmethod substructure [SetPartition :locus.set.logic.core.set/universal]
  [^SetPartition a, coll]

  (SetPartition.
    (restrict-partition (.-partition a) coll)))

; Functional partitions
; A functional partition on a set S is the partition of S that has as equivalence classes
; the kernel of a function operating on S.
(defprotocol StructuredFunctionalPartition
  "This protocol defines partitions of sets that are induced by the kernels of functions."

  (classifying-function [this]
    "Return the function that defines this partition."))

(deftype FunctionalPartition [coll func]
  ConcreteObject
  (underlying-set [this] coll)

  StructuredFunctionalPartition
  (classifying-function [this] func))

(derive FunctionalPartition ::functional-partition)

(defmethod equivalence-class-of ::functional-partition
  [partition x]

  (let [func (classifying-function partition)]
    (set
      (filter
        (fn [i]
          (= (func i) (func x)))
        (underlying-set partition)))))

(defmethod equivalence-classes ::functional-partition
  [partition]

  (let [func (classifying-function partition)]
    (pn
      (fn [a b]
        (= (func a) (func b)))
      (underlying-set partition))))

(defmethod equal? ::functional-partition
  [partition, a, b]

  (let [func (classifying-function partition)]
    (= (func a) (func b))))

; Convert a set partition into a functional partition
(defn functionalize-set-partition
  [partition]

  (let [coll (apply union partition)
        sorted-partition (vec (seq partition))
        resulting-mapping (apply
                            merge
                            (map-indexed
                              (fn [i v]
                                (into
                                  {}
                                  (map
                                    (fn [j]
                                      [j i])
                                    v)))
                              sorted-partition))]
    (FunctionalPartition. coll resulting-mapping)))

; Coproduct partitions
; A coproduct of set partitions is a partition of the coproduct of the underlying sets
; that preserves the underlying type identity.
(deftype CoproductPartition [partitions]
  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct (map underlying-set partitions))))

(derive CoproductPartition ::set-partition)

(defmethod equivalence-class-of CoproductPartition
  [^CoproductPartition coproduct-partition, [i v]]

  (let [partitions (.-partitions coproduct-partition)
        current-partition (nth partitions i)
        current-class (equivalence-class-of current-partition v)]
    (set
      (map
        (fn [new-value]
          (list i new-value))
        current-class))))

(defmethod equivalence-classes CoproductPartition
  [^CoproductPartition coproduct-partition]

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
      (map equivalence-classes (.-partitions coproduct-partition)))))

(defmethod equal? CoproductPartition
  [^CoproductPartition coproduct-partition, [i v], [j w]]

  (and
    (= i j)
    (equal? (nth (.-partitions coproduct-partition) i) v w)))

; Product partitions
; A product of set partitions is equivalent to the product of its underlying equivalence relations.
; Its underlying set is the cartesian product of each of the underlying sets of its partitions.
(deftype ProductPartition [partitions]
  ConcreteObject
  (underlying-set [this]
    (->CartesianProduct (map underlying-set partitions))))

(derive ProductPartition ::set-partition)

(defmethod equivalence-class-of ProductPartition
  [^ProductPartition product-partition, tuple]

  (let [partitions (.-partitions product-partition)]
    (apply
      cartesian-product
      (map-indexed
        (fn [i v]
          (equivalence-class-of (nth partitions i) v))
        tuple))))

(defmethod equivalence-classes ProductPartition
  [^ProductPartition product-partition]

  (set
    (map
      (fn [coll]
        (apply cartesian-product coll))
      (apply
        cartesian-product
        (map equivalence-classes (.-partitions product-partition))))))

(defmethod equal? ProductPartition
  [^ProductPartition product-partition, a, b]

  (let [partitions (.-partitions product-partition)]
    (and
      (= (count a) (count b) (count partitions))
      (every?
        (fn [i]
          (let [partition (nth partitions i)]
            (equal? partition (nth a i) (nth b i))))
        (range (count partitions))))))

; Test if the second partition is more equal than the first
(defn more-equal?
  [partition1 partition2]

  (every?
    (fn [[a b]]
      (equal? partition2 a b))
    (underlying-relation partition1)))

(defn less-equal?
  [partition1 partition2]

  (every?
    (fn [[a b]]
      (equal? partition1 a b))
    (underlying-relation partition2)))

; Get a quotient object from a presheaf of equivalence relations
(defmulti get-quotient type)

(defmethod get-quotient ::set-partition
  [partition]

  (equivalence-classes partition))

; Perform visualisation for set congruences
(defn create-clustered-equivalence-relation-digraph*
  [cluster-name labelings]

  (dot/subgraph
    (keyword cluster-name)
    [{:style "filled"
      :fillcolor "powderblue"}
     (map-indexed
       (fn [i labeling]
         (dot/subgraph
           (keyword (str cluster-name i))
           [{:style "filled"
             :fillcolor "white"}
            (map
              (fn [[k v]]
                [(.toString k) {:label (.toString v)}])
              labeling)]))
       labelings)]))

(defmethod visualize ::set-partition
  [partition]

  (letfn [(create-labeling-by-set-partition [family]
            (let [coll (apply union family)
                  ordered-coll (vec (seq coll))]
              (map
                (fn [elems]
                  (into
                    {}
                    (map
                      (fn [elem]
                        {(.indexOf ordered-coll elem) elem})
                      elems)))
                family)))]
    (output-graph!
      (dot/dot
        (dot/digraph
          [{:rankdir "LR"}
           (create-clustered-equivalence-relation-digraph*
             "cluster1"
             (create-labeling-by-set-partition (equivalence-classes partition)))])))))





