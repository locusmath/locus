(ns locus.matrix.combinatorics.degree-matrix
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.combinat.hypergraph.object :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

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

(defn display-degree-matrix
  [structure]

  (doseq [i (degree-matrix structure)]
    (prn i)))
