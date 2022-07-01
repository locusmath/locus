(ns locus.variety.projective.impl
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.ring.core.arithmetic :as arith]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.ideal.object :refer :all]
            [locus.ring.core.quotient-ring :refer :all]
            [locus.semigroup-algebra.core.object :refer :all]
            [locus.elementary.semigroup.free.free-semigroup :refer :all]))

; A projective variety much like an affine variety is determined by a set of polynomials.
; However, in this case, the projective variety should be determined by a set of
; homogeneous polynomials whose terms all have the same degree with one another. Then
; the homogeneous polynomials determine a variety in projective space.

(deftype ProjectiveVariety [ring vars polynomials])

(defmethod coordinate-ring ProjectiveVariety
  [variety]

  (->QuotientRing
    (semigroup-algebra (.ring variety) (free-commutative-monoid (.vars variety)))
    (.polynomials variety)))
