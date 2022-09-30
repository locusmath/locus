(ns locus.transcendental.functions.rings
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.module.vector.rset :refer :all])
  (:import (org.apache.commons.math3.analysis UnivariateFunction BivariateFunction TrivariateFunction)
           (org.apache.commons.math3.analysis.function Exp)))

; Ring of univariate real functions
; The apache commons math system provides general classes for dealing with univariate functions.
; In order to integrate the apache commons math classes into Locus we need to implement generic
; arithmetic operations on them using our own classes. Further, we define a helper class to define
; implementations of the univariate function interface using Clojure's functions.

(deftype UnivariateFn [func]
  UnivariateFunction
  (value [this x]
    (func x)))

(defmethod negate UnivariateFunction
  [^UnivariateFunction f]

  (UnivariateFn.
    (fn [i]
      (- (.value f i)))))

(defmethod add [UnivariateFunction UnivariateFunction]
  [^UnivariateFunction f, ^UnivariateFunction g]

  (UnivariateFn.
    (fn [i]
      (+ (.value f i) (.value g i)))))

(defmethod multiply [UnivariateFunction UnivariateFunction]
  [^UnivariateFunction f, ^UnivariateFunction g]

  (UnivariateFn.
    (fn [i]
      (* (.value f i) (.value g i)))))

; Rings of bivariate real functions
(deftype BivariateFn [func]
  BivariateFunction
  (value [this x y]
    (func x y)))

(defmethod negate BivariateFunction
  [^BivariateFunction f]

  (BivariateFn.
    (fn [x y]
      (- (.value f x y)))))

(defmethod add [BivariateFunction BivariateFunction]
  [^BivariateFunction f, ^BivariateFunction g]

  (BivariateFn.
    (fn [x y]
      (+ (.value f x y) (.value g x y)))))

(defmethod multiply [BivariateFunction BivariateFunction]
  [^BivariateFunction f, ^BivariateFunction g]

  (BivariateFn.
    (fn [x y]
      (* (.value f x y) (.value f x y)))))

; Rings of trivariate real functions
(deftype TrivariateFn [func]
  TrivariateFunction
  (value [this x y z]
    (func x y z)))

(defmethod negate TrivariateFunction
  [^TrivariateFunction f]

  (TrivariateFn.
    (fn [x y z]
      (- (.value f x y z)))))

(defmethod add [TrivariateFunction TrivariateFunction]
  [^TrivariateFunction f, ^TrivariateFunction g]

  (TrivariateFn.
    (fn [x y z]
      (+ (.value f x y z) (.value g x y z)))))

(defmethod multiply [TrivariateFunction TrivariateFunction]
  [^TrivariateFunction f, ^TrivariateFunction g]

  (TrivariateFn.
    (fn [x y z]
      (* (.value f x y z) (.value f x y z)))))


