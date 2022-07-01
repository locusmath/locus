(ns locus.number.complex.number
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.group-with-zero :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.semiring.core.object :refer :all]
            [locus.ring.core.arithmetic :refer :all]
            [locus.ring.core.protocols :refer :all])
  (:import (org.apache.commons.math3.complex Complex ComplexUtils)
           (locus.elementary.group.core.object Group)))

; Complex numbers
(defmethod print-method Complex [^Complex v ^java.io.Writer w]
  (.write w (str "#C" (.toString v))))

(defn complex-number
  [a b]

  (Complex. a b))

(defn real-part
  [^Complex n]

  (.getReal n))

(defn imaginary-part
  [^Complex n]

  (.getImaginary n))

(defn polar-to-complex
  [r theta]

  (ComplexUtils/polar2Complex r theta))

(defn complex-argument
  [^Complex n]

  (.getArgument n))

(defn complex-magnitude
  [^Complex n]

  (.abs n))

; The action of complex conjugation on the field of complex numbers
(defn complex-conjugate
  [^Complex n]

  (.conjugate n))

; The field of complex numbers
(defn complex-number?
  [n]

  (= (type n) Complex))

(defn purely-imaginary-complex-number?
  [n]

  (and
    (complex-number? n)
    (zero? (real-part n))))

(def complex-numbers
  (make-ring
    (Group.
      complex-number?
      (fn [[^Complex a, ^Complex b]]
        (.add a b))
      Complex/ZERO
      (fn [^Complex n]
        (.negate n)))
    (group-with-zero
      complex-number?
      (fn [[^Complex a, ^Complex b]]
        (.multiply a b))
      Complex/ONE
      (fn [^Complex n]
        (if (and (zero? (.getImaginary n))
                 (zero? (.getReal n)))
          0
          (.reciprocal n)))
      0)))

; The ring Z[i] of gaussian integers
(defn gaussian-integer?
  [n]

  (and
    (complex-number? n)
    (let [rp (.getReal ^Complex n)
          ip (.getImaginary ^Complex n)]
      (and
        (== (int rp) rp)
        (== (int ip) ip)))))

(def gaussian-integers
  (make-ring
    (Group.
      gaussian-integer?
      (fn [[^Complex a, ^Complex b]]
        (.add a b))
      Complex/ZERO
      (fn [^Complex n] (.negate n)))
    (->Monoid
      gaussian-integer?
      (fn [[^Complex a, ^Complex b]]
        (.multiply a b))
      Complex/ONE)))

; Generic complex operations
(defmethod add [Complex Complex]
  [^Complex a, ^Complex b]

  (.add a b))

(defmethod negate Complex
  [^Complex a]

  (.negate a))

(defmethod multiply [Complex Complex]
  [^Complex a, ^Complex b]

  (.multiply a b))

(defmethod reciprocal Complex
  [^Complex a]

  (.reciprocal a))

(defmethod get-semiring Complex
  [complex] complex-numbers)