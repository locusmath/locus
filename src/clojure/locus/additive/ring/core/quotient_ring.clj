(ns locus.additive.ring.core.quotient-ring
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
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