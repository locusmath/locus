(ns locus.number.quaternion.number
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.group-with-zero :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semifield.core.object :refer :all]
            [locus.additive.field.core.object :refer :all])
  (:import (org.apache.commons.math3.complex Quaternion)
           (locus.algebra.group.core.object Group)))

; Division rings of quaternions
(defmethod print-method Quaternion [^Quaternion v ^java.io.Writer w]
  (.write w (str "#H" (.toString v))))

(defn quaternion
  [a b c d]

  (Quaternion. a b c d))

(defn quaternion?
  [n]

  (= (type n) Quaternion))

(def quaternions
  (make-ring
    (Group.
      quaternion?
      (fn [[^Quaternion a, ^Quaternion b]]
        (.add a b))
      Quaternion/ZERO
      (fn [^Quaternion n]
        (.subtract Quaternion/ZERO n)))
    (group-with-zero
      quaternion?
      (fn [[^Quaternion a, ^Quaternion b]]
        (.multiply a b))
      Quaternion/IDENTITY
      (fn [^Quaternion n]
        (.getInverse n))
      Quaternion/ZERO)))

; Generic quaternion operations
(defmethod add [Quaternion Quaternion]
  [^Quaternion a, ^Quaternion b]

  (.add a b))

(defmethod negate Quaternion
  [^Quaternion a]

  (.subtract Quaternion/ZERO a))

(defmethod multiply [Quaternion Quaternion]
  [^Quaternion a, ^Quaternion b]

  (.multiply a b))

(defmethod reciprocal Quaternion
  [^Quaternion a]

  (.getInverse a))

(defmethod get-semiring Quaternion
  [a] quaternions)
