(ns locus.variety.affine.impl
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.algebra.semigroup.free.free-semigroup :refer :all]
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