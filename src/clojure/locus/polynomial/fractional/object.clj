(ns locus.polynomial.fractional.object
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.module.vector.rset :refer :all]
            [locus.polynomial.core.object :refer :all])
  (:import (locus.polynomial.core.object Polynomial)))

; Elements of the fields of fractions of polynomial rings
(deftype RationalExpression [numerator denominator])

(defn numerator-polynomial
  [^RationalExpression expr]

  (.numerator expr))

(defn denominator-polynomial
  [^RationalExpression expr]

  (.denominator expr))

; Generic conversion routines
(defmulti to-rational-expression type)

(defmethod to-rational-expression RationalExpression
  [expr] expr)

(defmethod to-rational-expression Polynomial
  [expr]

  (RationalExpression. expr (one-polynomial (ring-of-coefficients expr))))

; Negation
(defmethod negate RationalExpression
  [^RationalExpression expr]

  (RationalExpression. (- (numerator-polynomial expr)) (denominator-polynomial expr)))

(defmethod reciprocal Polynomial
  [^Polynomial polynomial]

  (RationalExpression. (one-polynomial (ring-of-coefficients polynomial)) polynomial))

(defmethod reciprocal RationalExpression
  [^RationalExpression expr]

  (RationalExpression. (.denominator expr) (.numerator expr)))

(defmethod multiply [RationalExpression RationalExpression]
  [a b]

  (RationalExpression.
    (* (numerator-polynomial a) (numerator-polynomial b))
    (* (denominator-polynomial a) (denominator-polynomial b))))

(defmethod add [RationalExpression RationalExpression]
  [a b]

  (RationalExpression.
    (+ (* (numerator-polynomial a) (denominator-polynomial b))
       (* (numerator-polynomial b) (denominator-polynomial a)))
    (* (denominator-polynomial a) (denominator-polynomial b))))

; Ontology of rational expressions
(defn rational-expression?
  [expr]

  (= (type expr) RationalExpression))

