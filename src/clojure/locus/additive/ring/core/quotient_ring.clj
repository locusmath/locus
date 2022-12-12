(ns locus.additive.ring.core.quotient-ring
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.monoid.arithmetic :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.ring.ideal.object :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.ideal.object :refer :all])
  (:import (locus.additive.ring.ideal.object Ideal)))

; A general class for describing quotient rings, such as the coordinate rings of varieties,
; which is described in terms of a ring and a generating set of its set of ideals
(deftype QuotientRing [ring gens])

(derive QuotientRing :locus.additive.base.core.protocols/ring)

; Get the underlying ideal of a quotient ring
(defn ideal
  [^QuotientRing quotient-ring]

  (Ideal. (.ring quotient-ring) (.gens quotient-ring)))

; Get the quotient ring of an ideal
(defn make-quotient-ring
  [^Ideal ideal]

  (QuotientRing. (.ring ideal) (.gens ideal)))

; The coordinate rings of algebraic varieties
(defmulti coordinate-ring type)