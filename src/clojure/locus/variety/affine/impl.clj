(ns locus.variety.affine.impl
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.ring.core.arithmetic :as arith]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.ideal.object :refer :all]
            [locus.ring.core.quotient-ring :refer :all]
            [locus.semigroup-algebra.core.object :refer :all]
            [locus.elementary.semigroup.free.free-semigroup :refer :all]))

; An affine variety is defined by a base ring, a set of variables, and a
; set of polynomials whose solutions determine the resulting space.
(deftype AffineVariety [ring vars polynomials])

(defmethod coordinate-ring AffineVariety
  [variety]

  (->QuotientRing
    (semigroup-algebra (.ring variety) (free-commutative-monoid (.vars variety)))
    (.polynomials variety)))