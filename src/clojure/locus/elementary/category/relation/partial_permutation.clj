(ns locus.elementary.category.relation.partial-permutation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.effects.local.permutation :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.elementary.category.relation.partial-function :refer :all]
            [locus.elementary.category.relation.partial-bijection :refer :all]
            [locus.elementary.category.relation.partial-transformation :refer :all])
  (:import (locus.elementary.category.relation.partial_transformation PartialTransformation)
           (clojure.lang IPersistentMap)
           (locus.elementary.category.relation.partial_bijection PartialBijection)))

; Partial permutations:
; One to one partial transformations are called partial permutations, or sometimes charts.
; A special case is that of an atomic chart, which can be defined by a single ordered pair
; on a set. These atomic charts are the action of preorders. Every partial permutation can be
; determined by its decomposition into nilpotent and permutation parts.
(deftype PartialPermutation [domain codomain coll forward backward]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] coll)

  Invertible
  (inv [this]
    (PartialPermutation.
      codomain
      domain
      coll
      backward
      forward))

  clojure.lang.IFn
  (invoke [this arg]
    (forward arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive PartialPermutation :locus.elementary.category.relation.partial-function/partial-permutation)

; Defined domains and codomains
(defmethod defined-domain PartialPermutation
  [^PartialPermutation func]

  (.domain func))

(defmethod partial-function-image PartialPermutation
  [^PartialPermutation func]

  (.codomain func))

; Composition and identities in the category of partial permutations
(defn identity-partial-permutation
  [coll]

  (PartialPermutation.
    coll
    coll
    coll
    (fn [x] x)
    (fn [x] x)))

(defmethod compose* :locus.elementary.category.relation.partial-function/partial-permutation
  [a b]

  (let [new-domain (set
                     (filter
                       (fn [i]
                         (let [next-val (b i)]
                           (boolean
                             ((defined-domain a) next-val))))
                       (defined-domain b)))
        new-codomain (set
                       (map
                         (fn [i]
                           (a (b i)))
                         new-domain))]
    (PartialPermutation.
      new-domain
      new-codomain
      (source-object b)
      (comp (.forward a) (.forward b))
      (comp (.backward a) (.backward b)))))

; Relational partial permutations
(defn relational-partial-permutation
  ([rel] (relational-partial-permutation (vertices rel) rel))
  ([coll rel]
   (let [reverse-rel (transpose rel)]
     (PartialPermutation.
      (relation-domain rel)
      (relation-codomain rel)
      coll
      (fn [i]
        (call rel i))
      (fn [i]
        (call reverse-rel i))))))

; Conversion routines
(defmulti to-partial-permutation type)

(defmethod to-partial-permutation PartialPermutation
  [func] func)

(defmethod to-partial-permutation :locus.base.logic.core.set/universal
  [coll] (relational-partial-transformation coll))

(defmethod to-partial-permutation IPersistentMap
  [coll]

  (if (not (distinct-seq? (seq (vals coll))))
    (throw (new IllegalArgumentException))
    (let [in (set (keys coll))
          out (set (vals coll))
          all-values (union in out)]
      (->PartialPermutation
        in
        out
        all-values
        coll
        (into {} (map (comp vec reverse) coll))))))

(defmethod to-partial-permutation :locus.base.logic.structure.protocols/permutation
  [permutation]

  (let [coll (outputs permutation)]
    (->PartialPermutation coll coll coll permutation (inv permutation))))

(defmethod to-partial-permutation PartialBijection
  [^PartialBijection func]

  (->PartialPermutation
    (defined-domain func)
    (partial-function-image func)
    (union (source-object func) (target-object func))
    (.-forward func)
    (.-backward func)))

(defmethod to-partial-permutation :locus.elementary.copresheaf.core.protocols/bijection
  [bijection] (to-partial-permutation (to-partial-bijection bijection)))

; Atomic charts are the simplest means of generating preorders by an action
; Semigroups of atomic charts are all equivalent to preorders. They can be formed,
; for example from the object preorders of categories.
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

(derive AtomicChart :locus.elementary.category.relation.partial-function/atomic-chart)

(defmethod print-method AtomicChart [^AtomicChart v, ^java.io.Writer w]
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

(defmethod to-partial-bijection AtomicChart
  [^AtomicChart func]

  (->PartialPermutation
    #{(.first func)}
    #{(.second func)}
    (.coll func)
    (fn [x]
      (.second func))
    (fn [x]
      (.first func))))

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
      (cartesian-power (set (range (inc n))) n))))

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