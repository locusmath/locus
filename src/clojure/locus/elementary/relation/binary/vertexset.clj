(ns locus.elementary.relation.binary.vertexset
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all])
  (:import [locus.elementary.relation.binary.sr SeqableRelation]))

; This file provides several supporting utility functions for dealing with subsets of
; binary relations, as well as an ontology of classes of vertex subsets of binary relations.

; Strong and ordinary precedence relations
(defn ordinary-precedence?
  [rel s1 s2]

  (not
   (empty?
    (filter
     (fn [[a b]]
       (rel (list a b)))
     (cartesian-product s1 s2)))))

(defn strong-precedence?
  [rel s1 s2]

  (every?
   (fn [[a b]]
     (rel (list a b)))
   (cartesian-product s1 s2)))

; With this we can define the relation quotient
(defn relation-quotient
  [rel partition]

  (set
   (filter
    (fn [[a b]]
      (ordinary-precedence? rel a b))
    (cartesian-power partition 2))))

; The inflation and deflation of relations
(defn deflate-relation
  [rel]

  (relation-quotient rel (vertex-equality rel)))

(defn inflate-relation
  [coll rel func]

  (SeqableRelation.
   coll
   (fn [[a b]]
     (rel (list (func a) (func b))))
   {}))

; Lets get classified subrelations
(defn classified-subrelations
  [rel pred]

  (set
   (filter
    (partial pred rel)
    (power-set (vertices rel)))))

; Ideals and filters
(defn ideals
  "The extrema closure of the principal ideals."
  [order]

  (set
   (filter
    (fn [coll]
      (every?
       (fn [i]
         (superset? (list (direct-predecessors order i) coll)))
       coll))
    (power-set (vertices order)))))

(defn filters
  "The extrema closure of the principal filters."
  [order]

  (set
   (filter
    (fn [coll]
      (every?
       (fn [i]
         (superset? (list (direct-successors order i) coll)))
       coll))
    (power-set (vertices order)))))

(defn principal-ideals
  [rel]

  (set
   (map
    (partial direct-predecessors rel)
    (vertices rel))))

(defn principal-filters
  [rel]

  (set
   (map
    (partial direct-successors rel)
    (vertices rel))))

(defn lower-closure
  [rel coll]

  (apply union (map (partial predecessors rel) coll)))

(defn upper-closure
  [rel coll]

  (apply union (map (partial successors rel) coll)))

; The ontology of vertex sets
(defn vertex-set?
  [rel coll]

  (superset? (list coll (vertices rel))))

(defn ideal-vertex-set?
  [rel coll]

  (every?
   (fn [x]
     (superset? (list (direct-predecessors rel x) coll)))
   coll))

(defn filter-vertex-set?
  [rel coll]

  (every?
   (fn [x]
     (superset? (list (direct-successors rel x) coll)))
   coll))

(defn vertex-cut-set?
  [rel coll]

  (let [new-rel (subrelation rel (difference (vertices rel) coll))]
    (< (count (weak-connectivity rel))
       (count (weak-connectivity new-rel)))))

(defn lower-closure-generator?
  [rel coll]

  (superset? (list (maximal-vertices rel) coll)))

(defn upper-closure-generator?
  [rel coll]

  (superset? (list (maximal-vertices rel) coll)))

(defn weak-connectivity-closed?
  [rel coll]

  (let [components (weak-connectivity rel)
        intersecting-components (filter
                                 (fn [i]
                                   (not (empty? (intersection coll i))))
                                 components)]
    (= coll (apply union intersecting-components))))

(defn strong-connectivity-closed?
  [rel coll]

  (let [components (strong-connectivity rel)
        intersecting-components (filter
                                 (fn [i]
                                   (not (empty? (intersection coll i))))
                                 components)]
    (= coll (apply union intersecting-components))))

(defn convex-vertex-set?
  [rel coll]

  (let [lower (lower-closure rel coll)
        upper (upper-closure rel coll)]
    (every?
     (fn [i]
       (or
        (not (contains? lower i))
        (not (contains? upper i))
        (contains? coll i)))
     (vertices rel))))
