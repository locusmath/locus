(ns locus.elementary.relational.function.partial-transformation
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.relational.function.partial-set-function :refer :all])
  (:import (clojure.lang PersistentArrayMap PersistentHashSet PersistentHashMap)))

; A partial transformation is an endomorphism in the category of sets and
; partial functions. In our ontology, we define partial transformations as special
; types of partial set functions by using derive. Partial transformations are distinguished
; from ordinary functions by the fact that they are only defined on a subset of their inputs.
(deftype PartialTransformation
  [domain coll func]

  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] coll)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PartialTransformation :locus.elementary.relational.function.partial-set-function/partial-set-function)

; Defined domains of partial transformations
(defmethod defined-domain PartialTransformation
  [^PartialTransformation func]

  (.domain func))

; Composition and identities in terms of partial transformations
(defn identity-partial-transformation
  [coll]

  (PartialTransformation.
    coll
    coll
    (fn [x]
      x)))

(defmethod compose* PartialTransformation
  [a b]

  (let [new-coll (set
                   (filter
                     (fn [i]
                       (boolean
                         ((defined-domain a) (b i))))
                     (.coll b)))]
    (PartialTransformation.
      new-coll
      (source-object b)
      (comp (.func a) (.func b)))))

; The action preorder of a partial transformation
(defn partial-transformation-preorder
  [func]

  (cl preorder? (underlying-relation func)))

; Partial transformation producers
(defn empty-partial-transformation
  [coll]

  (PartialTransformation.
    #{}
    coll
    {}))

(defn map-to-partial-transformation
  [coll]

  (let [all-values (union (set (keys coll)) (set (vals coll)))
        source-values (set (keys coll))]
    (PartialTransformation.
      source-values
      all-values
      (fn [i]
        (get coll i)))))

(defn relational-partial-transformation
  [coll rel]

  (let [source-values (relation-domain rel)]
    (PartialTransformation.
      source-values
      coll
      (fn [i]
        (call rel i)))))

(defn relation-to-partial-transformation
  [rel]

  (relational-partial-transformation (vertices rel) rel))

; Conversion multimethod
(defmulti to-partial-transformation type)

(defmethod to-partial-transformation PartialTransformation
  [func] func)

(defmethod to-partial-transformation PersistentArrayMap
  [coll] (map-to-partial-transformation coll))

(defmethod to-partial-transformation PersistentHashMap
  [coll] (map-to-partial-transformation coll))

; Convert partial transformations into partial set functions
(defmethod to-partial-set-function PartialTransformation
  [func]

  (->PartialSetFunction
    (defined-domain func)
    (source-object func)
    (target-object func)
    (fn [i]
      (func i))))

; Join and meet of partial transformations
(defn joinable-partial-transformations?
  [a b]

  (every?
    (fn [i]
      (= (a i) (b i)))
    (intersection (defined-domain a) (defined-domain b))))

(defn meet-partial-transformations
  [& transformations]

  (when (not (empty? transformations))
    (let [common-domain (filter
                          (fn [i]
                            (equal-seq?
                              (map
                                (fn [transformation]
                                  (transformation i))
                                transformations)))
                          (apply
                            intersection
                            (map defined-domain transformations)))]
      (PartialTransformation.
        common-domain
        (apply intersection (map target-object transformations))
        (fn [i]
          ((.func (first transformations)) i))))))

(defn join-partial-transformations
  [& transformations]

  (letfn [(to-map [transformation]
            (apply
              merge
              (map
                (fn [i]
                  {i (transformation i)})
                (defined-domain transformation))))]
    (PartialTransformation.
      (apply union (map defined-domain transformations))
      (apply union (map target-object transformations))
      (apply merge (map to-map transformations)))))

; Charts:
; One to one partial transformations are called charts. Every chart can be
; reduced to a nilpotent and a permutation part. A special case is an
; atomic chart which has only one transition.
(deftype AtomicChart
  [coll first second]

  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] coll)

  Object
  (toString [this]
    (str first " -> " second))

  Invertible
  (inv [this]
    (AtomicChart. coll second first))

  clojure.lang.IFn
  (invoke [this arg]
    (when (= arg first) second))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive AtomicChart :locus.elementary.relational.function.partial-set-function/atomic-chart)

(defmethod print-method AtomicChart [^AtomicChart v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod defined-domain AtomicChart
  [^AtomicChart chart] #{(.first chart)})

; Conversion routines
(defmethod to-partial-transformation AtomicChart
  [^AtomicChart func]

  (->PartialTransformation
    #{(.first func)}
    (.coll func)
    (fn [x] (.second func))))

; Composition of atomic charts
(defmethod compose* AtomicChart
  [f g]

  (let [source (source-object g)]
    (if (= (.second g) (.first f))
      (AtomicChart. source (.first g) (.second f))
      (empty-partial-transformation source))))

; A preorder is nothing more then a semigroup of atomic charts
(defn preorder-atomic-charts
  [rel]

  (let [coll (vertices rel)]
    (map
      (fn [[a b]]
        (AtomicChart. coll a b))
      rel)))

; Chart creation functions
(defn forwards-map
  [coll]

  (if (<= (count coll) 1)
    {}
    (apply
      merge
      (map
        (fn [i]
          {(nth coll i) (nth coll (inc i))})
        (range (dec (count coll)))))))

(defn permutation-map
  [coll]

  (if (empty? coll)
    {}
    (apply
      merge
      (map
        (fn [i]
          (if (= i (dec (count coll)))
            {(nth coll i) (first coll)}
            {(nth coll i) (nth coll (inc i))}))
        (range (count coll))))))

(defn create-chart
  [nilpotent-part permutation-part]

  (PartialTransformation.
    (union
      (apply union (map (comp set butlast) nilpotent-part))
      (apply union (map set permutation-part)))
    (union
      (apply union (map set nilpotent-part))
      (apply union (map set permutation-part)))
    (merge
      (apply
        merge
        (map forwards-map nilpotent-part))
      (apply
        merge
        (map permutation-map permutation-part)))))

; Decomposition of charts
(defn in-defined-dom?
  [func x]

  (boolean ((defined-domain func) x)))

(defn partial-transformation-applications
  [func x]

  (let [domain (.coll func)]
    (loop [current-element x
           collected-values []]
      (cond
        (contains? (set collected-values) current-element) collected-values
        (not (in-defined-dom? func current-element)) (conj collected-values current-element)
        :else (if (not (contains? domain current-element))
                (conj collected-values current-element)
                (recur
                  (func current-element)
                  (conj collected-values current-element)))))))

(defn decompose-chart
  [chart]

  (letfn [(decompose-relation [rel]
            (loop [remaining-elements (seq (weakly-connected-components rel))
                   permutation-part []
                   nilpotent-part []]
              (if (empty? remaining-elements)
                [nilpotent-part permutation-part]
                (let [current-component (first remaining-elements)
                      is-permutation? (= (count (vertices current-component))
                                         (count current-component))
                      component-sequence (partial-transformation-applications
                                           chart
                                           (if is-permutation?
                                             (first (vertices current-component))
                                             (first (minimal-vertices current-component))))]
                  (recur
                    (rest remaining-elements)
                    (if is-permutation?
                      (conj permutation-part component-sequence)
                      permutation-part)
                    (if is-permutation?
                      nilpotent-part
                      (conj nilpotent-part component-sequence)))))))]
    (let [rel (underlying-relation chart)
          coll (vertices rel)
          missing-elements (difference
                             (source-object chart)
                             coll)
          [nilpotent-part permutation-part] (decompose-relation rel)]
      [(vec
         (concat
           nilpotent-part
           (map
             (fn [missing-element]
               [missing-element])
             missing-elements)))
       permutation-part])))

(def nilpotent-part
  (comp first decompose-chart))

(def permutation-part
  (comp second decompose-chart))

; Inversion of charts
(defn invert-chart
  [chart]

  (let [new-rel (transpose (underlying-relation chart))
        coll (source-object chart)]
    (PartialTransformation.
      (relation-domain new-rel)
      coll
      (fn [i]
        (call new-rel i)))))

; Enumeration facilities for dealing with partial transformations
(defn enumerate-partial-transformations
  [coll]

  (let [n (count coll)]
    (map
      (fn [nums]
        (relational-partial-transformation
          coll
          (apply
            union
            (map-indexed
              (fn [i v]
                (if (= v 0)
                  #{}
                  #{(list (nth coll i) (nth coll (dec v)))}))
              nums))))
      (seqable-cartesian-power (set (range (inc n))) n))))

(defn number-of-partial-transformations
  [n]

  (int (.pow (BigInteger/valueOf n) (inc n))))

(defn partial-transformations
  [coll]

  (let [ordered-coll (vec coll)]
    (->SeqableUniversal
      (fn [transformation]
        (and
          (partial-transformation? transformation)
          (= (source-object transformation)
            (target-object transformation)
            coll)))
      (enumerate-partial-transformations ordered-coll)
      {:count (number-of-partial-transformations (count coll))})))


; We now also need something that deals specifically with the enumeration
; and description of charts, which are a special type of relation
(defn number-of-partial-permutations
  [n]

  (apply
    +
    (map
      (fn [k]
        (* (factorial k)
           (binomial-coefficient n k)
           (binomial-coefficient n k)))
      (range 0 (inc n)))))

(defn enumerate-chart-relations
  [inset outset]

  (if (empty? inset)
    '(#{})
    (let [current-input (first inset)]
      (concat
        (enumerate-chart-relations (disj inset current-input) outset)
        (mapcat
          (fn [i]
            (let [current-pair (list current-input i)]
              (map
                (fn [chart]
                  (conj chart current-pair))
                (enumerate-chart-relations (disj inset current-input) (disj outset i)))))
          outset)))))

(defn charts
  [coll]

  (->SeqableUniversal
    (fn [chart]
      (and
        (partial-permutation? chart)
        (= (source-object chart)
           (target-object chart)
           coll)))
    (map
      (fn [i]
        (relational-partial-transformation
          coll
          i))
      (enumerate-chart-relations coll coll))
    {:count (number-of-partial-permutations (count coll))}))

; We need some special method of dealing with preorder partial transformations
(defn preorder-partial-transformation-relations
  [rel]

  (map
    (fn [coll]
      (apply union coll))
    (apply
      cartesian-product
      (map
        (fn [vertex]
          (conj
            (set
              (map
                (fn [successor]
                  #{(list vertex successor)})
                (successors rel vertex)))
            #{}))
        (vertices rel)))))

; We also need some way of getting all charts associated to a partition
(defn partition-chart-relations
  [partition]

  (map
    (partial apply union)
    (apply
      cartesian-product
      (map
        (fn [i]
          (set (enumerate-chart-relations i i)))
        partition))))

