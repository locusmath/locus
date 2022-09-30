(ns locus.additive.ring.element.ring-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.ring.core.object :refer :all])
  (:import (locus.additive.ring.core.object Ring)))

; General abstract class for ring elements
; This will allow us to integrate rings into our generic arithmetic system

(deftype RingElement [ring element]
  Element
  (parent [this] ring)

  IdentifiableInstance
  (unwrap [this] element))

(derive RingElement :locus.base.logic.structure.protocols/element)

(defmethod wrap Ring
  [ring elem]

  (->RingElement ring elem))

; Arithmetic operations for ring elements
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


