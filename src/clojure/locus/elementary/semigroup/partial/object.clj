(ns locus.elementary.semigroup.partial.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.category.partial.bijection :refer :all]
            [locus.elementary.category.partial.transformation :refer :all]
            [locus.elementary.category.partial.permutation :refer :all]))

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
(derive PartialTransformationSemigroup :locus.elementary.copresheaf.core.protocols/semigroup)

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