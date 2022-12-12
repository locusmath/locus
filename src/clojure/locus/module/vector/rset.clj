(ns locus.module.vector.rset
  (:require [locus.set.logic.core.set :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.algebra.group.term.signed-multiset :refer :all])
  (:import (locus.set.logic.core.set Multiset)
           (locus.algebra.group.term.signed_multiset SignedMultiset)))

; Modules of ringed sets
; Ringed sets are generalizes of sets, multisets, signed sets, real valued sets,
; etc to general rings. They are an important concept in our construction of
; free modules and related theories.

(defprotocol RingedSet
  "A ringed set is any structure that has the data of a function f : S to R, where R can be any
  ring. This is a vast generalisation of the idea of a set to include signed multisets, rational
  valued sets, etc. The terms is S and the ring of coefficients is R. The mapping from S to
  R is defined by the coefficient function."

  (ring-of-coefficients [this]
    "The ring of outputs of the coefficient mapping of the ringed set.")
  (terms [this]
    "The set of inputs of the coefficient mapping of the ringed set.")
  (coefficient [this arg]
    "The mapping that takes terms to values in the ring of coefficients."))

(deftype RSet [ring data]
  RingedSet
  (ring-of-coefficients [this] ring)
  (terms [this] (set (keys data)))
  (coefficient [this arg]
    (let [rval (get data arg)]
      (if (nil? rval) 0 rval)))

  java.lang.Object
  (toString [this]
    (str "#R" (.toString data))))

(defmethod print-method RSet [^RSet v ^java.io.Writer w]
  (.write w (.toString v)))

(extend-type SignedMultiset
  RingedSet
  (ring-of-coefficients [this] zz)
  (terms [this] (signed-support this))
  (coefficient [this x] (signed-multiplicity this x)))

; Creators for rsets, which are general sets over rings
(defmulti to-rset type)

(defmethod to-rset :default
  [coll]

  (RSet. nn (multiplicities-map coll)))

(defmethod to-rset Multiset
  [^Multiset coll]

  (RSet. nn (.multiplicities coll)))

(defmethod to-rset SignedMultiset
  [^SignedMultiset coll]

  (RSet. zz (.multiplicities coll)))

; Arithmetical operations on RSets which make them into modules
(defn zero-rset
  [ring]

  (RSet. ring {}))

(defn add-rsets
  [a b]

  (let [ring (ring-of-coefficients a)
        add (additive-semigroup ring)]
    (RSet.
      ring
      (into
        {}
        (for [i (union (terms a) (terms b))
              :let [v (add
                        (list
                          (coefficient a i)
                          (coefficient b i)))]
              :when (not (zero? v))]
          [i v])))))

(defn negate-rset
  [coll]

  (let [ring (ring-of-coefficients coll)
        inv (additive-inverse-function ring)]
    (RSet.
      ring
      (into
        {}
        (for [i (terms coll)]
          [i (inv (coefficient coll i))])))))

(defn scale-rset
  [coll n]

  (let [ring (ring-of-coefficients coll)
        mul (multiplicative-semigroup ring)]
    (RSet.
      ring
      (into
        {}
        (for [i (terms coll)]
          [i (mul (list n (coefficient coll i)))])))))

; Get a list of all coefficients
(defn coefficients
  [x]

  (set
    (map
      (fn [i]
        (coefficient x i))
      (terms x))))

