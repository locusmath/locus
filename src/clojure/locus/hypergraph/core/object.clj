(ns locus.hypergraph.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]))

; Hypergraphs are simple incidence structures
; In this sense, we can consider a hypergraph to be defined by a set of triples
; of an incidence structure that consists of vertices, edges, and flags describing
; which vertices belong to which edges. Then the naturally defined functor that
; takes any hypergraph to its corresponding span presheaf allows us to interpret
; the category of hypergraphs topos theoretically.

(deftype Hypergraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive Hypergraph :locus.elementary.function.core.protocols/structured-set)

(defn family->hypergraph
  [family]

  (let [coll (apply union family)]
    (Hypergraph.
      coll
      family)))

(defn edge-set
  [hypergraph]

  (.edges hypergraph))

(defn complement-hypergraph
  [hypergraph]

  (Hypergraph.
    (underlying-set hypergraph)
    (difference (power-set (underlying-set hypergraph)) (edge-set hypergraph))))

; Hypergraph statistics
(defn hypergraph-order
  [hypergraph]

  (count (underlying-set hypergraph)))

(defn hypergraph-size
  [hypergraph]

  (count (.edges hypergraph)))

(defn hypergraph-rank
  [hypergraph]

  (rank (edge-set hypergraph)))

; Ontology of hypergraphs
(defmulti hypergraph? type)

(defmethod hypergraph? Hypergraph
  [obj] true)

(defmethod hypergraph? :default
  [obj] false)

(defn graph?
  [obj]

  (and
    (hypergraph? obj)
    (nullfree-rank-two-family? (edge-set obj))))

(defn simple-graph?
  [obj]

  (and
    (hypergraph? obj)
    (binary-family? (edge-set obj))))

(defn uniform-hypergraph?
  [obj]

  (and
    (hypergraph? obj)
    (uniform-family? (edge-set obj))))

(defn ternary-hypergraph?
  [obj]

  (and
    (hypergraph? obj)
    (ternary-family? (edge-set obj))))

(defn quaternary-hypergraph?
  [obj]

  (and
    (hypergraph? obj)
    (quaternary-family? (edge-set obj))))





