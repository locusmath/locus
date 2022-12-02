(ns locus.elementary.group.term.signed-multiset
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.numeric.natural :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; Let G be a free abelian group over a set of generators S. Then the elements of the free abelian group
; are naturally all associated with a signed multiplicity, where the sign denotes rather or not
; the given element has been inverted. It follows that the elements of free abelian groups form
; a special data structure: the signed multiset and this file provides an implementation of that.

(use 'clojure.walk)

; Signed multisets data type
(deftype SignedMultiset [multiplicities]
  Object
  (toString [this]
    (str "*" (.toString multiplicities)))

  Invertible
  (inv [this]
    (SignedMultiset.
      (clojure.walk/walk
        (fn [[k v]]
          [k (- v)])
        identity
        multiplicities))))

(defmethod print-method SignedMultiset [^SignedMultiset v ^java.io.Writer w]
  (.write w ^String (.toString v)))

; The fundamental operation for converting collections to signed multisets
(defmulti to-signed-multiset type)

(defmethod to-signed-multiset :default
  [coll]

  (SignedMultiset. (.multiplicities (multiset coll))))

; Signed multiset functionality
(defn signed-support
  [sm]

  (set (keys (.multiplicities sm))))

(defn signed-multiplicity
  [sm key]

  (let [current-multiplicity ((.multiplicities sm) key)]
    (if (nil? current-multiplicity)
      0
      current-multiplicity)))

(defn signed-multiplicities
  [sm]

  (set
    (map
      (partial signed-multiplicity sm)
      (signed-support sm))))

(defn signed-order
  [sm]

  (apply + (signed-multiplicities sm)))

; Algebraic operations for free commutative groups
(defn iterate-signed-multiset
  [sm n]

  (SignedMultiset.
    (clojure.walk/walk
      (fn [[k v]]
        [k (* v n)])
      identity
      (.multiplicities ^SignedMultiset sm))))

(defn negate-signed-multiset
  [sm]

  (iterate-signed-multiset sm -1))

(defn add-signed-multisets
  [& signed-multisets]

  (if (empty? signed-multisets)
    (SignedMultiset. {})
    (let [all-keys (apply union (map signed-support signed-multisets))]
      (SignedMultiset.
        (let [combined-multiplicities (apply
                                        merge
                                        (for [key all-keys
                                              :let [sum (apply
                                                          +
                                                          (map
                                                            #(signed-multiplicity % key)
                                                            signed-multisets))]
                                              :when (not (zero? sum))]
                                          {key sum}))]
          (if (nil? combined-multiplicities)
            {}
            combined-multiplicities))))))

; Signed factorisation of rational numbers
(defn signed-factors
  [num]

  (add-signed-multisets
    (to-signed-multiset (factors (numerator num)))
    (inv (to-signed-multiset (factors (denominator num))))))

; Predicates for dealing with signed multisets
(defn signed-multiset?
  [coll]

  (= (type coll) SignedMultiset))


