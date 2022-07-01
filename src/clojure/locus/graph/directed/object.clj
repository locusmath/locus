(ns locus.graph.directed.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]))

; Digraph
; The category of digraphs can be interpreted topos theoretically in terms of the fundamental
; topos of quivers. In this context, the category of digraphs is simply the subcategory
; consisting of thin quivers. We provide the to-quiver method in order to interpret
; the category of directed graphs more topos theoretically.

(deftype Digraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive Digraph :locus.elementary.function.core.protocols/structured-set)

(defn digraph
  [rel]

  (Digraph. (vertices rel) rel))

(defmethod underlying-relation Digraph
  [^Digraph digraph]

  (.edges digraph))

(defmethod visualize Digraph
  [^Digraph digraph] (visualize (underlying-relation digraph)))

(defmethod to-quiver Digraph
  [^Digraph digraph]

  (thin-quiver
    (underlying-set digraph)
    (underlying-relation digraph)))

(defn digraph-order
  [digraph]

  (count (underlying-set digraph)))

(defn digraph-size
  [digraph]

  (count (underlying-relation digraph)))

(defn transpose-digraph
  [^Digraph digraph]

  (Digraph.
    (underlying-set digraph)
    (transpose (underlying-relation digraph))))

(defn complement-digraph
  [^Digraph digraph]

  (Digraph.
    (underlying-set digraph)
    (difference (complete-relation (underlying-set digraph)) (underlying-relation digraph))))

(defn out-neighbours
  [^Digraph digraph, x]

  (set
    (for [[a b] (underlying-relation digraph)
          :when (= a x)]
      b)))

(defn in-neighbours
  [^Digraph digraph, x]

  (set
    (for [[a b] (underlying-relation digraph)
          :when (= b x)]
      a)))

(defn sink-vertices
  [^Digraph digraph]

  (set
    (filter
      (fn [vertex]
        (empty? (out-neighbours digraph vertex)))
      (underlying-set digraph))))

(defn source-vertices
  [^Digraph digraph]

  (set
    (filter
      (fn [vertex]
        (empty? (in-neighbours digraph vertex)))
      (underlying-set digraph))))

(defn vertex-in-degree
  [^Digraph digraph, vertex]

  (count (in-neighbours digraph vertex)))

(defn vertex-out-degree
  [^Digraph digraph, vertex]

  (count (out-neighbours digraph vertex)))

(defn digraph-in-degree-sequence
  [^Digraph digraph]

  (map
    (fn [vertex]
      (vertex-in-degree digraph vertex))
    (underlying-set digraph)))

(defn digraph-out-degree-sequence
  [^Digraph digraph]

  (map
    (fn [vertex]
      (vertex-out-degree digraph vertex))
    (underlying-set digraph)))

; Ontology of directed graphs
(defn digraph?
  [digraph]

  (= (type digraph) Digraph))

(defn irreflexive-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (irreflexive? (underlying-relation digraph))))

(defn reflexive-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (reflexive? (underlying-relation digraph))))

(defn antisymmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (antisymmetric-digraph? (underlying-relation digraph))))

(defn asymmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (asymmetric? (underlying-relation digraph))))

(defn symmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (symmetric-binary-relation? (underlying-relation digraph))))

(defn directed-acyclic-graph?
  [digraph]

  (and
    (digraph? digraph)
    (acyclic-relation? (underlying-relation digraph))))

(defn strongly-connected-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (strongly-connected-relation? (underlying-relation digraph))))

(defn weakly-connected-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (weakly-connected-relation? (underlying-relation digraph))))


