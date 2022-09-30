(ns locus.matrix.combinatorics.degree-matrix
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.combinat.hypergraph.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)))

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
