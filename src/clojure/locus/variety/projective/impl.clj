(ns locus.variety.projective.impl
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.additive.base.generic.arithmetic :as arith]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.ring.ideal.object :refer :all]
            [locus.additive.ring.core.quotient-ring :refer :all]
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
