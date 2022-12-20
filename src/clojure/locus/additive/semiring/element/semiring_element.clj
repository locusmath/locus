(ns locus.additive.semiring.element.semiring-element
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.semiring.core.object :refer :all]))

; General abstract class for semiring elements
; This will allow us to better handle semirings defined abstractly by pairs of semigroups
(deftype SemiringElement [semiring element]
  Element
  (parent [this] semiring)

  IdentifiableInstance
  (unwrap [this] element))

(derive SemiringElement :locus.set.logic.structure.protocols/element)

(defmethod wrap :locus.additive.base.core.protocols/semiring
  [semiring elem]

  (->SemiringElement semiring elem))

; Arithmetic methods for semiring elements
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