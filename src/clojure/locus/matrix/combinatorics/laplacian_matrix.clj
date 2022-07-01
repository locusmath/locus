(ns locus.matrix.combinatorics.laplacian-matrix
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.hypergraph.incidence.incidence-structure :refer :all]
            [locus.hypergraph.core.object :refer :all]
            [locus.graph.undirected.object :refer :all]
            [locus.matrix.combinatorics.adjacency-matrix :refer :all]
            [locus.matrix.combinatorics.degree-matrix :refer :all]))

; Compute the laplacian matrix of a graph
(defn laplacian-matrix
  [graph]

  (build-square-matrix
    (fn [i j]
      (cond
        (= i j) (degree (edge-set graph) i)
        ((edge-set graph) #{i j}) -1
        :else 0))
    (count (underlying-set graph))))

(defn display-laplacian-matrix
  [graph]

  (doseq [i (laplacian-matrix graph)]
    (prn i)))
