(ns locus.topological.semigroup.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.topology.core.object :refer :all]
            [locus.ordered.semigroup.object :refer :all])
  (:import (locus.ordered.semigroup.object PreorderedSemigroup)))

; A topological semigroup is a semigroup internal to the concrete category Top of topological
; spaces and continuous maps between them. In a certain sense they can be treated as part
; of a categorical internalisation framework, which we also use to describe preordered
; semigroups and other structures.
(deftype TopologicalSemigroup [elems topology op]
  ConcreteObject
  (underlying-set [this] elems)

  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive TopologicalSemigroup :locus.set.copresheaf.structure.core.protocols/semigroup)

; Underlying preorders and topologies of topological semigroups
(defmethod underlying-semigroup TopologicalSemigroup
  [^TopologicalSemigroup semigroup]

  (.-op semigroup))

(defmethod topology TopologicalSemigroup
  [^TopologicalSemigroup semigroup]

  (.-topology semigroup))

; Underlying relations and multirelations can be derived from underlying quivers
(defmethod underlying-multirelation TopologicalSemigroup
  [^TopologicalSemigroup semigroup] (underlying-multirelation (underlying-quiver semigroup)))

(defmethod underlying-relation TopologicalSemigroup
  [^TopologicalSemigroup semigroup] (underlying-relation (underlying-quiver semigroup)))

; Constructors for special types of semigroups
(defn discrete-semigroup
  [semigroup]

  (->TopologicalSemigroup
    (underlying-set semigroup)
    (discrete-topology (underlying-set semigroup))
    (underlying-semigroup semigroup)))

(defn indiscrete-semigroup
  [semigroup]

  (->TopologicalSemigroup
    (underlying-set semigroup)
    (indiscrete-topology (underlying-set semigroup))
    (underlying-semigroup semigroup)))

; Conversion routines for topological semigroups
(defmulti to-topological-semigroup type)

(defmethod to-topological-semigroup TopologicalSemigroup
  [^TopologicalSemigroup semigroup] semigroup)

(defmethod to-topological-semigroup PreorderedSemigroup
  [^PreorderedSemigroup semigroup]

  (->TopologicalSemigroup
    (underlying-set semigroup)
    (alexandrov-topology (underlying-preorder semigroup))
    (underlying-semigroup semigroup)))

; Ontology of topological semigroups
(defn topological-semigroup?
  [obj]

  (= (type obj) TopologicalSemigroup))

(defn topological-monoid?
  [obj]

  (and
    (topological-semigroup? obj)
    (monoid? (underlying-semigroup obj))))

(defn discrete-semigroup?
  [obj]

  (and
    (topological-semigroup? obj)
    (discrete-topology? (topology obj))))

(defn indiscrete-semigroup?
  [obj]

  (and
    (topological-semigroup? obj)
    (indiscrete-topology? (topology obj))))

(defn discrete-monoid?
  [obj]

  (and
    (topological-semigroup? obj)
    (monoid? (underlying-semigroup obj))
    (discrete-topology? (topology obj))))

(defn indiscrete-monoid?
  [obj]

  (and
    (topological-semigroup? obj)
    (monoid? (underlying-semigroup obj))
    (indiscrete-topology? (topology obj))))