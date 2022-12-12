(ns locus.combinat.hypergraph.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.copresheaf.incidence.system.multifamily :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]))

; Hypergraphs are simple incidence structures
; In this sense, we can consider a hypergraph to be defined by a set of triples
; of an incidence structure that consists of vertices, edges, and flags describing
; which vertices belong to which edges. Then the naturally defined functor that
; takes any hypergraph to its corresponding span presheaf allows us to interpret
; the category of hypergraphs topos theoretically.

(deftype Hypergraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive Hypergraph :locus.set.logic.structure.protocols/structured-set)

(defn edge-set
  [hypergraph]

  (.edges hypergraph))

(defn complement-hypergraph
  [hypergraph]

  (Hypergraph.
    (underlying-set hypergraph)
    (difference
      (power-set (underlying-set hypergraph))
      (edge-set hypergraph))))

; Hypergraph constructors
(defn hypergraph
  ([family]
   (let [coll (apply union family)]
     (Hypergraph.
       coll
       family)))
  ([coll family]
   (Hypergraph. coll family)))

(defn complete-hypergraph
  [coll]

  (hypergraph coll (power-set coll)))

(defn empty-hypergraph
  [coll]

  (hypergraph coll #{}))

; Support for graphs as special cases of hypergraphs
(defn graph
  ([family]
   (Hypergraph. (apply union family) family))
  ([coll family]
   (Hypergraph. coll family)))

(defn line-graph
  [graph]

  (graph
    (edge-set graph)
    (set
      (for [[a b] (cartesian-power (edge-set graph) 2)
            :when (not (empty? (intersection a b)))]
        #{a b}))))

(defn johnson-graph
  [coll k]

  (let [elems (selections coll k)]
    (graph
      elems
      (set
        (filter
          (fn [pair]
            (= (count (apply intersection pair)) (dec k)))
          (selections elems 2))))))

(defn kneser-graph
  [coll k]

  (let [elems (selections coll k)]
    (graph
      elems
      (set
        (filter
          (fn [pair]
            (empty? (apply intersection pair)))
          (selections elems 2))))))

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

(defn empty-hypergraph?
  [obj]

  (and
    (hypergraph? obj)
    (empty? (edge-set obj))))

(defn complete-hypergraph?
  [obj]

  (and
    (hypergraph? obj)
    (power-set? (edge-set obj))))

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

(defn complete-graph?
  [obj]

  (and
    (graph? obj)
    (= (complete-dependency-family (underlying-set obj)) (edge-set obj))))

(defn complete-simple-graph?
  [obj]

  (and
    (graph? obj)
    (= (selections (underlying-set obj) 2) (edge-set obj))))

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





