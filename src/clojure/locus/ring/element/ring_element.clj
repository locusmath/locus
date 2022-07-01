(ns locus.ring.element.ring-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.object :refer :all]
            [locus.ring.core.arithmetic :refer :all]))

; General abstract class for ring elements elements
; This will allow us to integrate rings into our generic arithmetic system

(deftype RingElement [ring element])

(defmethod negate RingElement
  [^RingElement a]

  (let [ring (.ring a)]
    (RingElement.
      ring
      (invert-element (additive-semigroup ring) (.element a)))))

(defmethod add [RingElement RingElement]
  [^RingElement a, ^RingElement b]

  (let [ring (.ring a)]
    (RingElement.
      ring
      ((additive-semigroup ring) (list (.element a) (.element b))))))

(defmethod multiply [RingElement RingElement]
  [^RingElement a, ^RingElement b]

  (let [ring (.ring a)]
    (RingElement.
      ring
      ((multiplicative-semigroup ring) (list (.element a) (.element b))))))

(defmethod get-semiring RingElement
  [^RingElement a]

  (.ring a))






