(ns locus.elementary.relation.binary.vertices
  (:require [clojure.set]
            [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]))

; The purpose of this file is simply to provide all the
; different functions relate to vertices of binary
; relations that we need in our work.

; Predecessors and successors
(defn direct-predecessors
  [rel vertex]

  (set (for [[a b] rel
             :when (= vertex b)]
         a)))

(defn direct-successors
  [rel vertex]

  (set (for [[a b] rel
             :when (= vertex a)]
         b)))

(defn proper-direct-predecessors
  [rel vertex]

  (disj (direct-predecessors rel vertex) vertex))

(defn proper-direct-successors
  [rel vertex]

  (disj (direct-successors rel vertex) vertex))

(defn successors
  [rel a]

  (letfn [(get-targets [rel added to-add]
            (if (superset? (list to-add added))
              added
              (get-targets
               rel
               (union added to-add)
               (apply union (map (partial direct-successors rel) to-add)))))]
    (get-targets rel #{} (union #{a} (direct-successors rel a)))))

(defn predecessors
  [rel a]

  (letfn [(get-sources [rel added to-add]
            (if (superset? (list to-add added))
              added
              (get-sources
               rel
               (union added to-add)
               (apply union (map (partial direct-predecessors rel) to-add)))))]
    (get-sources rel #{} (union #{a} (direct-predecessors rel a)))))

(defn direct-neighborhood
  [rel vertex]

  (union (direct-predecessors rel vertex)
         (direct-successors rel vertex)))

(defn proper-direct-neighborhood
  [rel vertex]

  (disj (direct-neighborhood rel vertex) vertex))

; Output and input degrees
(defn out-degree
  [rel a]

  (count (direct-successors rel a)))

(defn in-degree
  [rel a]

  (count (direct-predecessors rel a)))

(defn multidomain
  [rel]

  (multiset (map first rel)))

(defn multicodomain
  [rel]

  (multiset (map second rel)))

; Proper out degree and in degree
(defn proper-out-degree
  [rel a]

  (count (proper-direct-successors rel a)))

(defn proper-in-degree
  [rel a]

  (count (proper-direct-predecessors rel a)))

; Pair degrees
(defn pair-degree
  [rel pair]

  (let [[a b] (seq pair)]
    (+ (if (rel (list a b)) 1 0)
       (if (rel (list b a)) 1 0))))

; Classified vertices
(defn classified-vertices
  [rel pred]

  (set
   (filter
    (partial pred rel)
    (vertices rel))))

(defn minimal-vertices
  [rel]

  (set
   (filter
    (fn [i]
      (empty? (proper-direct-predecessors rel i)))
    (vertices rel))))

(defn maximal-vertices
  [rel]

  (set
   (filter
    (fn [i]
      (empty? (proper-direct-successors rel i)))
    (vertices rel))))

; Get maximal and minimal vertices for vertex sets
(defn maximal-member-vertices
  [rel coll]

  (difference
    coll
    (set
      (for [[a b] rel
           :when (and
                   (boolean (coll a))
                   (boolean (coll b))
                   (not= a b))]
       a))))

(defn minimal-member-vertices
  [rel coll]

  (difference
    coll
    (set
      (for [[a b] rel
            :when (and
                    (boolean (coll a))
                    (boolean (coll b))
                    (not= a b))]
        b))))

; Ontology of vertices
(defn vertex?
  [rel vertex]

  (contains? (vertices rel) vertex))

(defn minimal-vertex?
  [rel vertex]

  (empty? (proper-direct-predecessors rel vertex)))

(defn maximal-vertex?
  [rel vertex]

  (empty? (proper-direct-successors rel vertex)))

(def extremal-vertex?
  (union
   minimal-vertex?
   maximal-vertex?))

(defn enclosed-vertex?
  [rel vertex]

  (not (extremal-vertex? rel vertex)))

(def isolated-vertex?
  (intersection
   minimal-vertex?
   maximal-vertex?))

(defn reflexive-vertex?
  [rel vertex]

  (rel (list vertex vertex)))

(defn symmetric-vertex?
  [rel vertex]

  (= (direct-successors rel vertex)
     (direct-predecessors rel vertex)))

(defn antisymmetric-vertex?
  [rel vertex]

  (empty?
   (intersection
    (proper-direct-successors rel vertex)
    (proper-direct-predecessors rel vertex))))

(defn unique-output-vertex?
  [rel vertex]

  (<= (out-degree rel vertex) 1))

(defn unique-input-vertex?
  [rel vertex]

  (<= (in-degree rel vertex) 1))

(defn central-vertex?
  [rel vertex]

  (let [coll (vertices rel)]
    (= coll
       (direct-predecessors rel vertex)
       (direct-successors rel vertex))))

(defn lower-bound-vertex?
  [rel vertex]

  (= (vertices rel)
     (direct-successors rel vertex)))

(defn upper-bound-vertex?
  [rel vertex]

  (= (vertices rel)
     (direct-predecessors rel vertex)))
