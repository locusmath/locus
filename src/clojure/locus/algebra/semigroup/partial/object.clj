(ns locus.algebra.semigroup.partial.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.set.action.core.protocols :refer :all]
            [locus.hyper.mapping.function :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.partial.mapping.transformation :refer :all]
            [locus.partial.mapping.bijection :refer :all]
            [locus.partial.mapping.permutation :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

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
(derive PartialTransformationSemigroup :locus.set.copresheaf.structure.core.protocols/semigroup)

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
    (->Hyperfunction
      coll
      coll
      (fn [i]
        (if (contains? domain i)
          #{(partial-transformation i)}
          #{})))))