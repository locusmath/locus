(ns locus.polynomial.univariate.real-polynomial
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all])
  (:import (org.apache.commons.math3.analysis.polynomials PolynomialFunction PolynomialsUtils)
           (locus.algebra.group.core.object Group)
           (locus.algebra.semigroup.monoid.object Monoid)))

; Make apache commons math polynomial functions get pretty printed
(defmethod print-method PolynomialFunction [^PolynomialFunction v ^java.io.Writer w]
  (.write w (.toString v)))

; Generic wrappers around apache commons math functionality
(defmethod negate PolynomialFunction
  [^PolynomialFunction func]

  (.negate func))

(defmethod add [PolynomialFunction PolynomialFunction]
  [a b]

  (.add a b))

(defmethod multiply [PolynomialFunction PolynomialFunction]
  [a b]

  (.multiply a b))

; Get the semiring of a real polynomial function
(defn real-univariate-polynomial?
  [polynomial]

  (= (type polynomial) PolynomialFunction))

(defn real-polynomial
  [& coefficients]

  (PolynomialFunction. (double-array coefficients)))

(def real-polynomial-ring
  (make-ring
    (Group.
      real-univariate-polynomial?
      (fn [[^PolynomialFunction a, ^PolynomialFunction b]]
        (.multiply a b))
      (real-polynomial 0)
      (fn [^PolynomialFunction a]
        (.negate a)))
    (Monoid.
      real-univariate-polynomial?
      (fn [[^PolynomialFunction a, ^PolynomialFunction b]]
        (.add a b))
      (real-polynomial 1))))

(defmethod get-semiring PolynomialFunction
  [func] real-polynomial-ring)

; Utility functions for dealing with polynomial functions
(def chebyshev-polynomial
  #(PolynomialsUtils/createChebyshevPolynomial %))

(def hermite-polynomial
  #(PolynomialsUtils/createHermitePolynomial %))

(def jacobi-polynomial
  #(PolynomialsUtils/createJacobiPolynomial %1 %2 %3))

(def laguerre-polynomial
  #(PolynomialsUtils/createLaguerrePolynomial %))

(def legendre-polynomial
  #(PolynomialsUtils/createLegendrePolynomial %))



