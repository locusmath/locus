(ns locus.elementary.action.effects.permutation
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.action.effects.transformation :refer :all])
  (:import (clojure.lang PersistentHashMap PersistentArrayMap)))

; We need some special way of dealing with transformations of sets
; that are also bijections when treated as functions.
(deftype Permutation [coll forward backward]
  ConcreteObject
  (underlying-set [this]
    coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this obj]
    (forward obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args))

  StructuredBijection
  (underlying-bijection [this]
    (->Bijection
      coll
      coll
      forward
      backward))

  Invertible
  (inv [this]
    (Permutation. coll backward forward))

  java.lang.Object
  (equals [this b]
    (and
      (equal-universals? (.coll this) (.coll ^Permutation b))
      (every?
        (fn [i]
          (= (this i) (b i)))
        coll))))

; Visualisation
(defmethod visualize Permutation
  [func] (visualize (underlying-function func)))

(defmethod compose* Permutation
  [f g]

  (Permutation.
    (inputs g)
    (comp (.forward f) (.forward g))
    (comp (.backward g) (.backward f))))

; A reusable routine for both array maps and hash maps
(defn map->permutation
  [coll]

  (Permutation.
    (set (keys coll))
    coll
    (apply array-map (apply concat (map reverse (seq coll))))))

; Conversion routines
(defmethod to-transformation Permutation
  [permutation]

  (->Transformation (underlying-set permutation) (.forward ^Permutation permutation)))

; We need some method for creating permutations
(defmulti to-permutation type)

(defmethod to-permutation PersistentArrayMap
  [coll] (map->permutation coll))

(defmethod to-permutation PersistentHashMap
  [coll] (map->permutation coll))

; Subalgebras and congruences of permutations
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

(defmethod sub Permutation
  [func] (sub (->Transformation (.coll func) (.forward func))))

(defmethod con Permutation
  [func] (con (->Transformation (.coll func) (.forward func))))

; It might also be nice to have products work on permutations
(defmethod product Permutation
  [& permutations]

  (Permutation.
    (apply cartesian-product (map underlying-set permutations))
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
    (apply cartesian-coproduct (map underlying-set permutations))
    (fn [[i v]]
      (list i ((nth permutations i) v)))
    (fn [[i v]]
      (list i ((.backward (nth permutations i)) v)))))

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

; Create an identity permutation
(defn identity-permutation
  [coll]

  (Permutation.
    coll
    identity
    identity))

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

; Create a numeric permutation
(defn numeric-permutation
  [coll]

  (Permutation.
    (seqable-interval 0 (count coll))
    (fn [i]
      (nth coll i))
    (fn [v]
      (.indexOf coll v))))

; This gets a permutation simply from a number
(defn nth-cycle-permutation
  [n]

  (Permutation.
    (seqable-interval 0 n)
    (fn [x]
      (mod (inc x) n))
    (fn [y]
      (if (zero? y)
        (dec n)
        (dec y)))))

; Special classes of total permutations
(defn total-permutation?
  [perm]

  (= (type perm) Permutation))

(defn even-total-permutation?
  [perm]

  (and
    (total-permutation? perm)
    (even? (permutation-parity perm))))

(defn odd-total-permutation?
  [perm]

  (and
    (total-permutation? perm)
    (odd? (permutation-parity perm))))

; Lens member permutations
(defn permutation-in-orbit?
  [func partition]

  (and
    (total-permutation? func)
    (preserved-transformation-congruence? func partition)))

(defn lens-member-permutation?
  [func active-partition preserved-partition]

  (and
    (total-permutation? func)
    (lens-member-transformation? func active-partition preserved-partition)))













