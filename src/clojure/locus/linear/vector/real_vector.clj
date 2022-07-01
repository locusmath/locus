(ns locus.linear.vector.real-vector
  (:import (org.apache.commons.math3.linear ArrayRealVector)))

; Vectors over the real numbers are provided by the apache commons math library
; The purpose of this file is to integration these apache commons vectors into
; the Clojure math system. In order to do that, we construct a number of
; different functions that wrap their apache commons math counterparts.
(defn real-vector
  [coll]

  (ArrayRealVector. (double-array coll)))

(defn zero-vector
  [n]

  (real-vector (repeat n 0)))

(defn magnitude
  [vec]

  (.getNorm vec))

(defn distance-between-vectors
  [a b]

  (.getDistance a b))

(defn get-unit-vector
  [a]

  (.unitVector a))

(defn scale-vector
  [vec n]

  (.mapMultiply vec n))

(defn negate-vector
  [n]

  (scale-vector n -1))

