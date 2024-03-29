(ns locus.order.lattice.term.lattice-equation-system
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.term.lattice-term :refer :all]
            [locus.order.lattice.term.lattice-equation :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.core.object Lattice)))

; A system of lattice equations occurs over a given lattice L and
; it consists of a collection of lattice equations over L that relate
; certain collections of variables over the lattice. A lattice equation system
; might emerge for example from a finitely presented lattice.
(deftype LatticeEquationSystem
  [lattice equations])

; Convert a lattice equation into a system of equations
(defn singular-lattice-equation-system
  [lattice equation]

  (LatticeEquationSystem. lattice (list equation)))

; Count the number of equations in an equation system
(defn number-of-lattice-equations
  [^LatticeEquationSystem equation-system]

  (count (.equations equation-system)))

; Check if a given system of lattice equations is satisfied
(defn satisfies-lattice-equation-system?
  [sys env]

  (let [join (join-fn (.lattice sys))
        meet (meet-fn (.lattice sys))]
    (every?
      (fn [equation]
        (satisfies-lattice-equation? join meet equation env))
      (.equations sys))))