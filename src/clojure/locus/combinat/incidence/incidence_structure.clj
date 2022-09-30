(ns locus.combinat.incidence.incidence-structure
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.combinat.hypergraph.object :refer :all]
            [locus.elementary.incidence.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.combinat.hypergraph.object Hypergraph)))

; Incidence structures
; An incidence structure is a triple consisting of points, lines, and flags. They are interpreted
; topos theoretically in terms of the topos of span presheaves over the category [1,2]. In our
; implementation flags have a point first order (fn [[point line]] ...)
(deftype IncidenceStructure [points lines flags]
  StructuredDiset
  (first-set [this] points)
  (second-set [this] lines))

(defn incident?
  [structure point line]

  ((.flags structure) (list point line)))

; Conversion routines to turn hypergraphs into incidence structures
(defmulti to-incidence-structure type)

(defmethod to-incidence-structure IncidenceStructure
  [structure] structure)

(defmethod to-incidence-structure Hypergraph
  [hypergraph]

  (let [points (underlying-set hypergraph)
        lines (edge-set hypergraph)]
    (IncidenceStructure.
      points
      lines
      (seqable-binary-relation
        points
        lines
        (fn [[point line]] (contains? line point))))))

; convert the incidence structure into a span copresheaf
(defn to-span-copresheaf
  [incidence-structure]

  (simple-span
    (.lines incidence-structure)
    (.points incidence-structure)
    (.flags incidence-structure)))

; Incidence structure related functionality
(defn points
  [structure]

  (.points structure))

(defn lines
  [structure]

  (.lines structure))

(defn flags
  [structure]

  (.flags structure))

(defn incident-points
  [structure line]

  (set
    (filter
      (fn [point]
        (incident? structure point line))
      (points structure))))

(defn incident-lines
  [structure point]

  (set
    (filter
      (fn [line]
        (incident? structure point line))
      (lines structure))))

(defn point-sets
  [structure]

  (set
    (map
      (fn [line]
        (incident-points structure line))
      (lines structure))))

(defn line-sets
  [structure]

  (set
    (map
      (fn [point]
        (incident-lines structure point))
      (points structure))))

(defn incidence-function
  [structure]

  (SetFunction.
    (.lines structure)
    (->PowerSet (.points structure))
    (fn [line]
      (incident-points structure line))))

(defn dual-incidence-structure
  [structure]

  (IncidenceStructure.
    (.lines structure)
    (.points structure)
    (transpose (.flags structure))))

(defn complement-incidence-structure
  [structure]

  (IncidenceStructure.
    (points structure)
    (lines structure)
    (fn [[point line]]
      (not (incident? structure point line)))))

; Get the degrees of points and lines in the incidence structure
(defn line-degree
  [structure line]

  (count (incident-points structure line)))

(defn point-degree
  [structure point]

  (count (incident-lines structure point)))

(defn point-degrees
  [structure]

  (map
    (fn [point]
      (point-degree structure point))
    (points structure)))

(defn line-degrees
  [structure]

  (map
    (fn [line]
      (line-degree structure line))
    (lines structure)))

(defn number-of-points
  [structure]

  (count (points structure)))

(defn number-of-lines
  [structure]

  (count (lines structure)))

(defn intersecting-blocks?
  [structure block1 block2]

  (not
    (empty?
      (filter
        (fn [point]
          (and
            (incident? structure point block1)
            (incident? structure point block2)))
        (points structure)))))

; Compute the levi graph of an incidence structure, this is defined by
; taking the given incidence structure and treating its flags as an
; edge set for a graph containing both points and lines as vertices.
(defn incidence-graph
  [structure]

  (let [edges (set
                (map
                  (fn [[point line]]
                    (set [(list 0 point) (list 1 line)]))
                  (flags structure)))]
    (graph edges)))

; The intersection graph of an incidence structure is another fundamental
; notion of the theory of incidence structures, which is defined for
; any incidence structure such as a hypergraph or set system.
(defn intersection-graph
  [structure]

  (let [blocks (set (lines structure))]
    (graph
      blocks
      (for [[a b] (cartesian-power blocks 2)
            :when (intersecting-blocks? structure a b)]
        (set (list a b))))))

; Ontology of incidence structures
(defn incidence-structure?
  [structure]

  (= (type structure) IncidenceStructure))

(defn regular-incidence-structure?
  [structure]

  (and
    (incidence-structure? structure)
    (equal-seq? (point-degrees structure))))

(defn uniform-incidence-structure?
  [structure]

  (and
    (incidence-structure? structure)
    (equal-seq? (line-degrees structure))))

