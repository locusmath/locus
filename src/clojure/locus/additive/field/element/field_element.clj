(ns locus.additive.field.element.field-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semifield.core.object :refer :all]
            [locus.additive.field.core.object :refer :all]))

; General abstract class for ring elements
; This will allow us to integrate rings into our generic arithmetic system
(deftype FieldElement [ring element])

(defmethod negate FieldElement
  [^FieldElement a]

  (let [ring (.ring a)]
    (FieldElement.
      ring
      (invert-element (additive-semigroup ring) (.element a)))))

(defmethod reciprocal FieldElement
  [^FieldElement a]

  (let [ring (.ring a)]
    (FieldElement.
      ring
      (invert-element (multiplicative-semigroup ring) (.element a)))))

(defmethod add [FieldElement FieldElement]
  [^FieldElement a, ^FieldElement b]

  (let [ring (.ring a)]
    (FieldElement.
      ring
      ((additive-semigroup ring) (list (.element a) (.element b))))))

(defmethod multiply [FieldElement FieldElement]
  [^FieldElement a, ^FieldElement b]

  (let [ring (.ring a)]
    (FieldElement.
      ring
      ((multiplicative-semigroup ring) (list (.element a) (.element b))))))

(defmethod get-semiring FieldElement
  [^FieldElement a]

  (.ring a))
