(ns locus.ring.core.quotient-ring
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
            [locus.ring.ideal.object :refer :all])
  (:import (locus.ring.ideal.object Ideal)))

; A general class for describing quotient rings, such as the coordinate rings of varieties,
; which is described in terms of a ring and a generating set of its set of ideals
(deftype QuotientRing [ring gens])

(derive QuotientRing :locus.ring.core.protocols/ring)

; Get the underlying ideal of a quotient ring
(defn ideal
  [^QuotientRing quotient-ring]

  (Ideal. (.ring quotient-ring) (.gens quotient-ring)))

; Get the quotient ring of an ideal
(defn quotient-ring
  [^Ideal ideal]

  (QuotientRing. (.ring ideal) (.gens ideal)))

; The coordinate rings of algebraic varieties
(defmulti coordinate-ring type)