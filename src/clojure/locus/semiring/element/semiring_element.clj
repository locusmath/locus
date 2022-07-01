(ns locus.semiring.element.semiring-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.semiring.core.object :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.arithmetic :refer :all]))

; General abstract class for semiring elements
; This will allow us to better handle semirings defined abstractly by pairs of semigroups
(deftype SemiringElement [semiring element])

(defmethod add [SemiringElement SemiringElement]
  [^SemiringElement a, ^SemiringElement b]

  (let [ring (.semiring a)]
    (SemiringElement.
      ring
      ((additive-semigroup ring) (list (.element a) (.element b))))))

(defmethod multiply [SemiringElement SemiringElement]
  [^SemiringElement a, ^SemiringElement b]

  (let [ring (.semiring a)]
    (SemiringElement.
      ring
      ((multiplicative-semigroup ring) (list (.element a) (.element b))))))

(defmethod get-semiring SemiringElement
  [^SemiringElement a]

  (.semiring a))



