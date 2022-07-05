(ns locus.matrix.combinatorics.degree-matrix
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.hypergraph.core.object :refer :all]
            [locus.hypergraph.core.graph :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)
           (locus.hypergraph.core.graph Graph)))

(defn build-diagonal-matrix
  [coll]

  (let [n (count coll)]
    (map
      (fn [y]
        (map
          (fn [x]
            (if (= x y)
              (nth coll x)
              0))
          (range n)))
      (range n))))

(defmulti degree-matrix type)

(defmethod degree-matrix :default
  [family]

  (build-diagonal-matrix
    (map
      (fn [i]
        (degree family i))
      (apply union family))))

(defmethod degree-matrix Graph
  [graph]

  (build-diagonal-matrix
    (let [edges (edge-set graph)]
      (map
       (fn [vertex]
         (degree edges vertex))
       (underlying-set graph)))))

(defn display-degree-matrix
  [structure]

  (doseq [i (degree-matrix structure)]
    (prn i)))
