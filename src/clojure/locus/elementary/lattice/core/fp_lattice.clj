(ns locus.elementary.lattice.core.fp-lattice
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]

            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.term.lattice-term :refer :all]
            [locus.elementary.lattice.term.lattice-equation :refer :all]
            [locus.elementary.lattice.term.lattice-equation-system :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)))

; Finitely presented lattices
; A finitely presented lattice can be described by a set of generators
; as well as a system of lattice equations on those generators. In this sense,
; they are like finitely presented monoids and other systems in abstract
; algebra that are defined by systems of equations.

(deftype FPLattice [gens relations])

(derive FPLattice :locus.elementary.function.core.protocols/lattice)

; Lattice theoretic generating sets
(defmulti lattice-generators type)

(defmethod lattice-generators :default
  [x]

  (objects x))

(defmethod lattice-generators FPLattice
  [^FPLattice x]

  (.gens x))

; Get the system of equations that defines the lattice
(defn lattice-equations
  [^FPLattice fp-lattice]

  (.relations fp-lattice))

; Create free finitely presented lattice from a set of generators
(defn free-fp-lattice
  [gens]

  (FPLattice. gens #{}))