(ns locus.matrix.combinatorics.adjacency-matrix
  (:require [locus.base.logic.core.set :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)))

; A basic utility helper function for creating square matrices like these
(defn build-matrix
  [func number-of-rows number-of-columns]

  (map
    (fn [y]
      (map
        (fn [x]
          (func y x))
        (range number-of-columns)))
    (range number-of-rows)))

(defn build-square-matrix
  [func n]

  (let [coll (range n)]
    (map
     (fn [y]
       (map
         (fn [x]
           (func y x))
         coll))
     coll)))

; Compute adjacency matrices over various different data structures based upon
; the dispatch of a multimethod over the type of the data structures.
(defmulti adjacency-matrix type)

(defmethod adjacency-matrix Quiver
  [quiv]

  (let [elems (objects quiv)
        sorted-elems (seq elems)]
    (build-square-matrix
      (fn [y x]
        (quiver-hom-cardinality quiv (nth sorted-elems x) (nth sorted-elems y)))
      (count elems))))

(defmethod adjacency-matrix :default
  [rel]

  (if (or (universal? rel) (multiset? rel))
    (let [elems (vertices rel)
         sorted-elems (seq elems)]
      (build-square-matrix
        (fn [y x]
          (multiplicity rel (list (nth sorted-elems x) (nth sorted-elems y))))
        (count elems)))
    (adjacency-matrix (to-quiver rel))))

(defn display-adjacency-matrix
  [rel]

  (let [matrix (adjacency-matrix rel)]
    (doseq [i matrix]
      (prn i))))