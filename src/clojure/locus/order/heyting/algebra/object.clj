(ns locus.order.heyting.algebra.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.boolean.algebra.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (locus.order.boolean.algebra.object BooleanAlgebra)))

; A heyting algebra is a bounded lattice that is also equipped with an operation of
; implication which can be used to produce a relative pseudo-complement of an
; element. The relevance of heyting algebras in topos theory is that every subobject
; lattice of an object of a topos such as a presheaf is a Heyting algebra. Additional
; examples of Heyting algebras include all boolean algebras.
(deftype HeytingAlgebra [elements join meet implication]
  ConcreteObject
  (underlying-set [this] elements)

  StructuredJoinSemilattice
  (join-fn [this] join)

  StructuredMeetSemilattice
  (meet-fn [this] meet)

  StructuredDiset
  (first-set [this] (join-precedence-relation elements join))
  (second-set [this] elements)

  StructuredQuiver
  (underlying-quiver [this] (relational-quiver (objects this) (morphisms this)))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver (first-set this) (second-set this) first second (fn [i] (list i i))))
  (identity-morphism-of [this x] (list x x))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (first-set this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Heyting algebras are lattices
(derive HeytingAlgebra :locus.set.copresheaf.structure.core.protocols/lattice)

; Underlying relations of heyting algebras
(defmethod underlying-relation HeytingAlgebra
  [alg]

  (first-set HeytingAlgebra))

; Visualisation of heyting algebras
(defmethod visualize HeytingAlgebra
  [alg]

  (visualize (covering-relation (underlying-relation alg))))

; Compute the heyting algebra of a finite distributive lattice
(defn submeets
  [lattice a b]

  (set
    (filter
      (fn [c]
        (preceding-lattice-elements? lattice (meet-elements lattice c a) b))
      (objects lattice))))

(defn implication
  [lattice a b]

  (let [coll (submeets lattice a b)]
    (if (empty? coll)
      (lower-bound lattice)
      (apply (partial join-elements lattice) coll))))

; Generalized conversion routines for Heyting algebras
(defmulti to-heyting-algebra type)

(defmethod to-heyting-algebra Lattice
  [lattice]

  (->HeytingAlgebra
    (underlying-set lattice)
    (join-fn lattice)
    (meet-fn lattice)
    (fn [a b]
      (implication lattice a b))))

(defmethod to-heyting-algebra BooleanAlgebra
  [alg]

  (->HeytingAlgebra
    (underlying-set alg)
    (join-fn alg)
    (meet-fn alg)
    (fn [a b]
      (join-elements alg (negate-boolean-algebra-element alg a) b))))

; Total order heyting algebras
(defn nth-total-order-heyting-algebra
  [n]

  (HeytingAlgebra.
    (->Upto (inc n))
    max
    min
    (fn [a b]
      (if (<= a b)
        n
        0))))

; Ontology of heyting algebras
(defn heyting-algebra?
  [x]

  (= (type x) HeytingAlgebra))




