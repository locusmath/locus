(ns locus.matrix.combinatorics.adjacency-matrix
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

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