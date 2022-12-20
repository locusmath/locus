(ns locus.additive.semifield.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all])
  (:import (locus.additive.semiring.core.object Semiring)))

; A skew semifield is an algebraic structure with addition, multiplication, and division
; but not necessarily negation. The most basic example is the semifield of non-negative
; rational numbers.
(deftype SkewSemifield [elems add mul]
  ConcreteObject
  (underlying-set [this] elems))

(derive SkewSemifield :locus.additive.base.core.protocols/skew-semifield)

(defmethod additive-semigroup SkewSemifield
  [^SkewSemifield semiring]

  (.add semiring))

(defmethod multiplicative-semigroup SkewSemifield
  [^SkewSemifield semiring]

  (.mul semiring))

; Constructors for semifields
; A semifield should be constructed by a semigroup and a group with zero
(defmethod make-ring [:locus.set.copresheaf.structure.core.protocols/semigroup,
                      :locus.set.copresheaf.structure.core.protocols/group-with-zero]
  [a b]

  (SkewSemifield (underlying-set a) a b))

; The non-negative rationals are the simplest example of a semifield
(def non-negative-rational-numbers
  (make-ring nonnegative-rational-addition nonnegative-rational-multiplication))


