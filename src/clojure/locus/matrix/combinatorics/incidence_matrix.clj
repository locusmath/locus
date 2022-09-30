(ns locus.matrix.combinatorics.incidence-matrix
  (:require [locus.base.logic.core.set :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.incidence.system.clan :refer :all]
            [locus.elementary.incidence.system.multiclan :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.combinat.hypergraph.object :refer :all]
            [locus.combinat.incidence.incidence-structure :refer :all])
  (:import (locus.combinat.incidence.incidence_structure IncidenceStructure)
           (locus.combinat.hypergraph.object Hypergraph)))

; Incidence matrices of various structures
; Such as incidence structures, hypergraphs, graphs, set systems, and multiset systems.
(defmulti incidence-matrix type)

(defn display-incidence-matrix
  [sys]

  (doseq [i (incidence-matrix sys)]
    (prn i)))

(defmethod incidence-matrix :default
  [sys]

  (let [elems (apply union (map support sys))
        sorted-elems (seq elems)]
    (map
      (fn [coll]
        (map
          (fn [v]
            (multiplicity coll v))
          sorted-elems))
      sys)))

(defmethod incidence-matrix IncidenceStructure
  [structure]

  (let [sorted-points (seq (points structure))]
    (letfn [(line->point-vector [sorted-points line]
              (map
                (fn [point]
                  (if (incident? structure point line) 1 0))
                sorted-points))]
      (map
        (fn [i]
          (line->point-vector sorted-points i))
        (lines structure)))))

(defmethod incidence-matrix Hypergraph
  [structure]

  (incidence-matrix (to-incidence-structure structure)))



