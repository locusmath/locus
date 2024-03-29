(ns locus.topology.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.total.object :refer :all]
            [locus.order.lattice.total.open-interval :refer :all]
            [locus.order.lattice.total.open-set :refer :all]
            [locus.lawvere.metric.core.object :refer :all]
            [locus.lawvere.metric.set.open-ball :refer :all]
            [locus.lawvere.metric.set.open-set :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (locus.order.lattice.total.object TotallyOrderedSet)
           (locus.lawvere.metric.core.object LawvereMetric)))

; A topological space is a base for a Grothendieck topos of sheaves.
; Topological spaces are therefore one of the major outlets for the
; geometric applications of topos theory. Topological spaces are also related
; to set systems through their sets of open sets. We develop topological
; spaces here with a view toward studying their Grothendieck topoi.
(deftype TopologicalSpace [points opens]
  ConcreteObject
  (underlying-set [this] points))

(derive ::topology :locus.set.logic.structure.protocols/structured-set)
(derive TopologicalSpace ::topology)

; The adjoint relationship between order and topology
(defn alexandrov-topology
  [preposet]

  (->TopologicalSpace
    (objects preposet)
    (filters (underlying-relation preposet))))

(defn specialization-preorder
  [topology]

  (->Preposet
    (underlying-set topology)
    (fn [[x y]]
      (every?
        (fn [open]
          (or (not (contains? open x))
              (contains? open y)))
        (.-opens topology)))))

; A topological multimethod
(defmulti topology type)

(defmethod topology TopologicalSpace
  [topology] topology)

(defmethod topology :default
  [coll]

  (TopologicalSpace. (dimembers coll) coll))

(defmethod topology LawvereMetric
  [metric]

  (TopologicalSpace.
    (underlying-set metric)
    (fn [open]
      (open-set-of-metric? metric open))))

(defmethod topology :locus.set.copresheaf.structure.core.protocols/thin-category
  [poset]

  (alexandrov-topology poset))

; The order topology of a totally ordered set is distinguished from the topology induced by a
; preorder under the adjoint relationship between order and topology.
(defn order-topology
  [order]

  (TopologicalSpace.
    (underlying-set order)
    (fn [open]
      (open-set-of-total-order? order open))))

; Special types of topological space
(defn discrete-topology
  [coll]

  (TopologicalSpace. coll (->PowerSet coll)))

(defn indiscrete-topology
  [coll]

  (if (empty? coll)
    (TopologicalSpace. #{} #{#{}})
    (TopologicalSpace. coll #{#{} coll})))

(defn partition-topology
  [coll]

  (TopologicalSpace. (dimembers coll) (cl alexandrov-family? coll)))

; A topological space can also be seen as a type of lattice
(defn lattice-of-open-sets
  [topology]

  (Lattice. (.opens topology) union intersection))

; Comparison of topological spaces and the lattice of topologies
(defn stronger-topology?
  [a b]

  (and
    (= (underlying-set a) (underlying-set b))
    (superset? (list (.opens a) (.opens b)))))

(defn join-topologies
  [& topologies]

  (TopologicalSpace.
    (underlying-set (first topologies))
    (cl extrema-closed? (apply union (map #(.opens %) topologies)))))

(defn meet-topologies
  [& topologies]

  (TopologicalSpace.
    (underlying-set (first topologies))
    (apply intersection (map #(.opens %) topologies))))

; The lattice of topological spaces
(defn topology?
  [space]

  (= (type space) TopologicalSpace))

(defn lattice-of-topological-spaces
  [coll]

  (->Lattice
    (fn [i]
      (and
        (topology? i)
        (= (underlying-set i) coll)))
    join-topologies
    meet-topologies))

; Ontology of topological spaces
(defn partition-topology?
  [space]

  (and
    (topology? space)
    (partition-family? (.opens space))))

(defn indiscrete-topology?
  [space]

  (and
    (topology? space)
    (max-size-two-universal? (.opens space))))

(defn discrete-topology?
  [space]

  (and
    (topology? space)
    (power-set? (.opens space))))



