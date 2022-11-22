(ns locus.order.boolean.algebra.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]))

; A boolean algebra is a thin category used to define boolean formulas
; Boolean formulas are defined by collections of clauses over literals
; A boolean algebra can also be classified as a special type of Heyting algebra
; or as a special type of distributive lattice.
(deftype BooleanAlgebra [literals]
  ConcreteObject
  (underlying-set [this] (->PowerSet literals))

  StructuredJoinSemilattice
  (join-fn [this] union)

  StructuredMeetSemilattice
  (meet-fn [this] intersection)

  StructuredDiset
  (first-set [this] (power-set-ordering literals))
  (second-set [this] (underlying-set this))

  StructuredQuiver
  (underlying-quiver [this] (relational-quiver (objects this) (morphisms this)))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (->UnitalQuiver
      (first-set this)
      (second-set this)
      first
      second
      (fn [i] (list i i))))
  (identity-morphism-of [this x]
    (list x x))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (first-set this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Compute the complement of an element of a boolean algebra
(defn negate-boolean-algebra-element
  [alg x]

  (difference (.literals alg) x))

; Ontology of boolean algebras as lattices
(derive BooleanAlgebra :locus.elementary.copresheaf.core.protocols/lattice)

; We need to be able to have some means of visualizing boolean algebras
(defmethod visualize BooleanAlgebra
  [ba]

  (visualize (covering-relation (underlying-relation (underlying-quiver ba)))))

