(ns locus.elementary.lattice.term.lattice-equation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.term.lattice-term :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.lattice.term.lattice_term LatticeTerm)))

; A lattice equation consists of a pair of lattice terms that are equated
; to one another. The lattice terms can be represented symbolically. The point of
; this lattice equation class is to represent some of the individual equations
; that togethe make up a system of lattice equations.

(deftype LatticeEquation [left right]
  Object
  (toString [this]
    (str "(= " left " " right ")")))

(defmethod print-method LatticeEquation [^LatticeEquation v ^java.io.Writer w]
  (.write w (.toString v)))

(defn left-term
  [^LatticeEquation lattice-equation]

  (LatticeTerm. (.left lattice-equation)))

(defn right-term
  [^LatticeEquation lattice-equation]

  (LatticeTerm. (.right lattice-equation)))

; Distributive laws for lattices
(defn meet-distribution-equation
  [[a b c]]

  (LatticeEquation.
    (list '* a (list '+ b c))
    (list '+ (list '* a b) (list '* a c))))

(defn join-distribution-equation
  [[a b c]]

  (LatticeEquation.
    (list '+ a (list '* b c))
    (list '* (list '+ a b) (list '+ a c))))

; Modular laws for lattices
(defn modular-identity
  [[a b c]]

  (LatticeEquation.
    (list '+ (list '* a b) (list '* c b))
    (list
      '*
      (list
        '+
        (list '* a b)
        c)
      b)))

(defn modular-predecessor-identity
  [[a b c]]

  (LatticeEquation.
    (list '+ a (list '* c b))
    (list '* (list '+ a c) b)))

; Determine equality using joins and meets with a fixed element
(defn join-equality-with
  [[a b c]]

  (LatticeEquation.
    (list '+ a c)
    (list '+ b c)))

(defn meet-equality-with
  [[a b c]]

  (LatticeEquation.
    (list '* a c)
    (list '* b c)))

; Lattice inequalities as equations
; a <= b means that a*b = a and a + b = b
; a >= b means that a*b = b and a + b = a
(defn lattice-predecessor-inequality
  [a b]

  (LatticeEquation.
    (.data (product (LatticeTerm. a) (LatticeTerm. b)))
    a))

(defn lattice-successor-inequality
  [a b]

  (LatticeEquation.
    (.data (product (LatticeTerm. a) (LatticeTerm. b)))
    b))

; Test if a given lattice equation is satisfied with respect to an environment mapping
(defn satisfies-lattice-equation?
  [join meet equation env]

  (= (apply-lattice-expression join meet (.left equation) env)
     (apply-lattice-expression join meet (.right equation) env)))

