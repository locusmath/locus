(ns locus.additive.semifield.element.semifield-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semifield.core.object :refer :all])
  (:import (locus.additive.semifield.core.object SkewSemifield)))

; General abstract class for semifield elements
; Semifields are distinguished by the presence of a division operation on them
(deftype SemifieldElement [semiring element]
  Element
  (parent [this] semiring)

  IdentifiableInstance
  (unwrap [this] element))

(derive SemifieldElement :locus.base.logic.structure.protocols/element)

(defmethod wrap SkewSemifield
  [semifield elem]

  (->SemifieldElement semifield elem))

; Arithmetic operations for semifield elements
(defmethod add [SemifieldElement SemifieldElement]
  [^SemifieldElement a, ^SemifieldElement b]

  (let [ring (.semiring a)]
    (SemifieldElement.
      ring
      ((additive-semigroup ring) (list (.element a) (.element b))))))

(defmethod multiply [SemifieldElement SemifieldElement]
  [^SemifieldElement a, ^SemifieldElement b]

  (let [ring (.semiring a)]
    (SemifieldElement.
      ring
      ((multiplicative-semigroup ring) (list (.element a) (.element b))))))

(defmethod reciprocal SemifieldElement
  [^SemifieldElement a]

  (let [ring (.semiring a)
        a-element (.element a)]
    (SemifieldElement.
      ring
      (invert-element (multiplicative-semigroup ring) a-element))))

(defmethod get-semiring SemifieldElement
  [^SemifieldElement a]

  (.semiring a))
