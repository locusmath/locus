(ns locus.transcendental.functions.special
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.ring.core.arithmetic :refer :all]
            [locus.transcendental.functions.rings :refer :all])
  (:import [org.apache.commons.math3.special Gamma Erf Beta BesselJ]
           [org.apache.commons.math3.analysis.function Abs Acos Acosh Add Asin Asinh Atan Atanh Atan2 HarmonicOscillator Divide Cosh Cos Ceil Cbrt Exp Expm1 Floor Gaussian Identity Inverse Constant Log10 Log1p Max Min Minus Multiply Pow Power Rint Signum Sin Sinc Sinh Sqrt Subtract Tan Tanh Ulp StepFunction Logit Log Sigmoid Logistic]
           (locus.transcendental.functions.rings UnivariateFn BivariateFn)))

; This is a simple interface to the special functions provided by the apache commons math system,
; so that they can more readily be used in Locus. Special functions include a number of
; functions that are not elementary.

; Create a bessel function
(defn make-bessel-function
  [n]

  (BesselJ. n))

(def gamma
  (UnivariateFn.
    (fn [n]
      (Gamma/gamma n))))

(def erf
  (UnivariateFn.
    (fn [n]
      (Erf/erf n))))

(def log-beta
  (BivariateFn.
    (fn [a b]
      (Beta/logBeta a b))))

; Constant function constructor
(defn make-constant-function
  [n] (Constant. n))

(defn make-harmonic-oscillator
  [a o p] (HarmonicOscillator. a o p))

(defn make-power-function
  [p] (Power. p))

(defn make-step-function
  [x y] (StepFunction. x y))

(defn make-logistic-function
  [k m b q a n] (Logistic. k m b q a n))

; Elementary transcendental functions
(def abs (Abs.))
(def acos (Acos.))
(def acosh (Acosh.))
(def add* (Add.))
(def asin (Asin.))
(def asinh (Asinh.))
(def atan (Atan.))
(def atan2 (Atan2.))
(def atanh (Atanh.))
(def cbrt (Cbrt.))
(def ceil (Ceil.))
(def cos (Cos.))
(def cosh (Cosh.))
(def divide* (Divide.))
(def exp (Exp.))
(def expm1 (Expm1.))
(def floor (Floor.))
(def gaussian (Gaussian.))
(def identity* (Identity.))
(def inverse (Inverse.))
(def log (Log.))
(def log10 (Log10.))
(def log1p (Log1p.))
(def logit (Logit.))
(def max* (Max.))
(def min* (Min.))
(def minus (Minus.))
(def multiply* (Multiply.))
(def pow (Pow.))
(def rint (Rint.))
(def sigmoid (Sigmoid.))
(def signum (Signum.))
(def sin (Sin.))
(def sinc (Sinc.))
(def sinh (Sinh.))
(def sqrt (Sqrt.))
(def subtract* (Subtract.))
(def tan (Tan.))
(def tanh (Tanh.))
(def ulp (Ulp.))