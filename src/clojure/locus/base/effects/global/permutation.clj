(ns locus.base.effects.global.permutation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.transformation :refer :all]
            [locus.base.invertible.function.object :refer :all])
  (:import (clojure.lang IPersistentMap)))

; Permutations
; A permutation is simply an automorphism in the topos Sets, which means thatit can be composed
; with itself, and it can be inverted.
(deftype Permutation [coll forward backward]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [coll coll]))

  Object
  (equals [this b]
    (and
      (equal-universals? (.coll this) (.coll ^Permutation b))
      (every?
        (fn [i]
          (= (this i) (b i)))
        coll)))

  Invertible
  (inv [this]
    (Permutation. coll backward forward))

  clojure.lang.IFn
  (invoke [this obj]
    (forward obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Permutation :locus.base.logic.structure.protocols/permutation)

; Convert permutations into transformations
(defmethod to-transformation Permutation
  [^Permutation permutation]

  (->Transformation (inputs permutation) (.forward permutation)))

; Generalized multimethods for converting things into permutations
(defmulti to-permutation type)

(defmethod to-permutation Permutation
  [permutation] permutation)

(defmethod to-permutation IPersistentMap
  [coll]

  (Permutation.
    (set (keys coll))
    coll
    (apply array-map (apply concat (map reverse (seq coll))))))

(defmethod to-permutation :locus.base.logic.structure.protocols/invertible-set-function
  [func]

  (if (not (equal-universals? (inputs func) (outputs func)))
    (throw (new IllegalArgumentException))
    (Permutation.
      (inputs func)
      func
      (inv func))))

(defmethod to-permutation :locus.base.logic.structure.protocols/set-function
  [func]

  (if (not (autofunction? func))
    (throw (new IllegalArgumentException))
    (Permutation.
      (inputs func)
      (fn [x]
        (func x))
      (fn [x]
        (first (fiber func x))))))

(defn numeric-permutation
  [coll]

  (Permutation.
    (->Upto (count coll))
    (fn [i]
      (nth coll i))
    (fn [v]
      (.indexOf coll v))))

; Create an involution as a permutation by a partition
(defn involution-permutation
  [partition]

  (letfn [(apply-partition [x]
            (let [part (projection partition x)]
              (if (= (count part) 1)
                (first part)
                (first (disj part x)))))]
    (->Permutation
      (apply union partition)
      apply-partition
      apply-partition)))

; Composition and identities in the subcategory of permutations
(defn identity-permutation
  [coll]

  (Permutation.
    coll
    identity
    identity))

(defmethod compose* Permutation
  [f g]

  (Permutation.
    (inputs g)
    (comp (.forward f) (.forward g))
    (comp (.backward g) (.backward f))))

; It might also be nice to have products work on permutations
(defmethod product Permutation
  [& permutations]

  (Permutation.
    (apply cartesian-product (map inputs permutations))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth permutations i) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((.backward (nth permutations i)) v))
        coll))))

(defmethod coproduct Permutation
  [& permutations]

  (Permutation.
    (apply cartesian-coproduct (map inputs permutations))
    (fn [[i v]]
      (list i ((nth permutations i) v)))
    (fn [[i v]]
      (list i ((.backward (nth permutations i)) v)))))

; Subobjects and quotients of permutations
(defn restrict-permutation
  [permutation coll]

  (Permutation. coll (.forward permutation) (.backward permutation)))

(defn quotient-permutation
  [permutation partition]

  (Permutation.
    partition
    (fn [part]
      (projection partition (permutation (first part))))
    (fn [part]
      (projection partition ((inv permutation) (first part))))))

; The cycle decomposition of a permutation
(defn cycle-at-point
  [permutation x]

  (loop [cval x
         current-cycle []
         seen-values #{}]
    (if (contains? seen-values cval)
      current-cycle
      (recur
        (permutation cval)
        (conj current-cycle cval)
        (conj seen-values cval)))))

(defn cycle-decomposition
  [permutation]

  (let [coll (underlying-set permutation)]
    (loop [remaining-values coll
           cycles []]
      (if (empty? remaining-values)
        cycles
        (let [selected-element (first remaining-values)
              selected-cycle (cycle-at-point permutation selected-element)
              selected-cycle-elements (set selected-cycle)]
          (recur
            (difference remaining-values selected-cycle-elements)
            (conj cycles selected-cycle)))))))

; Compute the orbits of a permutation
(defn permutation-components
  [permutation]

  (set (map set (cycle-decomposition permutation))))

(defn cycle-signature
  [permutation]

  (multiset (map count (cycle-decomposition permutation))))

(defn permutation-period
  [permutation]

  (loop [cval permutation
         i 1]
    (let [next-val (compose cval permutation)]
      (if (= next-val permutation)
        i
        (recur next-val (inc i))))))

(defn permutation-parity
  [perm]

  (mod
    (apply + (map #(mod (- % 1) 2) (cycle-signature perm)))
    2))

; This is a special method for creating permutations
(defn permutation
  [coll]

  (letfn [(cycle-map [coll]
            (if (empty? coll)
              {}
              (let [n (count coll)]
                (apply
                  merge
                  (map
                    (fn [i]
                      {(nth coll i) (nth coll (mod (inc i) n))})
                    (range (count coll)))))))]
    (to-permutation
      (apply
        merge
        (map
          (fn [i]
            (cycle-map i))
          coll)))))

; This gets a permutation simply from a number
(defn nth-cycle-permutation
  [n]

  (Permutation.
    (->Upto n)
    (fn [x]
      (mod (inc x) n))
    (fn [y]
      (if (zero? y)
        (dec n)
        (dec y)))))

; Special classes of permutations
(defn even-permutation?
  [perm]

  (and
    (autofunction? perm)
    (even? (permutation-parity perm))))

(defn odd-permutation?
  [perm]

  (and
    (autofunction? perm)
    (odd? (permutation-parity perm))))

(defn cycle-permutation?
  [perm]

  (and
    (autofunction? perm)
    (<= (count (transformation-components perm)) 1)))

; Lens member permutations
(defn permutation-in-orbit?
  [func partition]

  (and
    (autofunction? func)
    (preserved-transformation-congruence? func partition)))

(defn lens-member-permutation?
  [func active-partition preserved-partition]

  (and
    (autofunction? func)
    (lens-member-transformation? func active-partition preserved-partition)))
