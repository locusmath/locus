(ns locus.elementary.semigroup.partial.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.action.partial.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.relational.relation.set-relation :refer :all]
            [locus.elementary.relational.function.partial-set-function :refer :all]
            [locus.elementary.relational.function.partial-transformation :refer :all]))

; Partial transformation semigroups
(deftype PartialTransformationSemigroup [semigroup coll func]
  ConcreteObject
  (underlying-set [this] (underlying-set semigroup))

  StructuredDiset
  (first-set [this] (first-set semigroup))
  (second-set [this] (second-set semigroup))

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver (underlying-set semigroup) 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation (underlying-set semigroup)))
  (outputs [this] (underlying-set semigroup))

  clojure.lang.IFn
  (invoke [this obj] (semigroup obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Semigroups
(derive PartialTransformationSemigroup :locus.elementary.function.core.protocols/semigroup)

; Convert partial transformation semigroups into partial action systems
(defmethod to-partial-action-system PartialTransformationSemigroup
  [^PartialTransformationSemigroup structure]

  (->PartialActionSystem
    (underlying-set (.semigroup structure))
    (.coll structure)
    (.func structure)))

; The semigroup of atomic charts describes a preorder as a type of action
(defn atomic-charts-semigroup
  [rel]

  (let [coll (vertices rel)]
    (PartialTransformationSemigroup.
      (edges-semigroup rel)
      coll
      (fn [edge]
        (if (empty? edge)
          (->PartialTransformation #{} coll identity)
          (->AtomicChart coll (first edge) (second edge)))))))

; Convert a morphism to a relation in the sense of a relational semigroupoid
(defn morphism-to-relation
  [structure elem]

  (let [coll (.coll structure)
        partial-transformation ((.func structure) elem)
        domain (defined-domain partial-transformation)]
    (->SetRelation
      coll
      coll
      (fn [i]
        (if (contains? domain i)
          #{(partial-transformation i)}
          #{})))))