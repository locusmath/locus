(ns locus.matrix.combinatorics.laplacian-matrix
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.combinat.incidence.incidence-structure :refer :all]
            [locus.combinat.hypergraph.object :refer :all]
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
