(ns locus.ab.vector.real-set
  (:require [locus.set.logic.core.set :refer :all]
            [locus.algebra.group.term.signed-multiset :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.field.core.object :refer :all]
            [locus.ab.vector.rset :refer :all])
  (:import (locus.set.logic.core.set Multiset)
           (locus.algebra.group.term.signed_multiset SignedMultiset)))

(use 'clojure.walk)

; Real valued sets
; A real-valued set is simply an object of a vector space over the real numbers.
(deftype RealSet [data]
  RingedSet
  (ring-of-coefficients [this] qq)
  (terms [this] (set (keys data)))
  (coefficient [this x]
    (let [rval (get data x)]
      (if (nil? rval)
        0
        rval))))

(defmethod print-method RealSet [^RealSet v ^java.io.Writer w]
  (.write w ^String (.toString v)))

; Create real valued sets
(defmulti to-real-set type)

(defmethod to-real-set RealSet
  [x] x)

(defmethod to-real-set SignedMultiset
  [x] (RealSet. (.multiplicities x)))

; Arithmetic operations in modules of real valued sets
(defn negate-real-set
  [^RealSet rs]

  (RealSet.
    (clojure.walk/walk
      (fn [[k v]]
        [k (- v)])
      identity
      (.data rs))))

(defn add-real-sets
  [& real-sets]

  (if (empty? real-sets)
    (RealSet. {})
    (let [all-terms (apply union (map terms real-sets))]
      (RealSet.
        (let [combined-multiplicities (apply
                                        merge
                                        (for [key all-terms
                                              :let [sum (apply
                                                          +
                                                          (map
                                                            #(coefficient % key)
                                                            real-sets))]
                                              :when (not (zero? sum))]
                                          {key sum}))]
          (if (nil? combined-multiplicities)
            {}
            combined-multiplicities))))))

; Ontology of real valued sets
(defn real-set?
  [x]

  (= (type x) RealSet))


