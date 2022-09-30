(ns locus.variety.affine.impl
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.semigroup.free.free-semigroup :refer :all]
            [locus.additive.base.generic.arithmetic :as arith]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.ring.core.quotient-ring :refer :all]
            [locus.additive.ring.ideal.object :refer :all]
            [locus.semigroup-algebra.core.object :refer :all]))

; An affine variety is defined by a base ring, a set of variables, and a
; set of polynomials whose solutions determine the resulting space.
(deftype AffineVariety [ring vars polynomials])

(defmethod coordinate-ring AffineVariety
  [variety]

  (->QuotientRing
    (semigroup-algebra (.ring variety) (free-commutative-monoid (.vars variety)))
    (.polynomials variety)))