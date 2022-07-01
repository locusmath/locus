(ns locus.elementary.incidence.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; Objects in the topos Sets^[1,2]
; Span copresheafs can be used to define hypergraphs and their generalisations
(deftype Span [flags edges vertices efn vfn])

; Components of the span copresheaf
(defn span-flags
  [^Span span]

  (.flags span))

(defn span-vertices
  [^Span span]

  (.vertices span))

(defn span-edges
  [^Span span]

  (.edges span))

(defn edge-fn
  [^Span span]

  (.efn span))

(defn vertex-fn
  [^Span span]

  (.vfn span))

(defn edge-component
  [^Span span, flag]

  ((.efn span) flag))

(defn vertex-component
  [^Span span, flag]

  ((.vfn span) flag))

(defn edge-function
  [^Span span]

  (SetFunction.
    (span-flags span)
    (span-edges span)
    (fn [flag]
      (edge-component span flag))))

(defn vertex-function
  [^Span span]

  (SetFunction.
    (span-flags span)
    (span-edges span)
    (fn [flag]
      (vertex-component span flag))))

; Basic properties of span copresheafs
(def span-order
  (comp count span-vertices))

(def span-size
  (comp count span-edges))

(def span-cardinality-sum
  (comp count span-flags))

; Duality in the incidence topos
(defn dual-span
  [^Span span]

  (Span.
    (span-flags span)
    (span-vertices span)
    (span-edges span)
    (vertex-fn span)
    (edge-fn span)))

; Flag aquisition functions
(defn get-edge-flags
  [^Span span, edge]

  (let [efn (edge-fn span)]
    (filter
      (fn [flag]
        (= (efn flag) edge))
      (span-flags span))))

(defn get-vertex-flags
  [^Span span, vertex]

  (let [vfn (vertex-fn span)]
    (filter
      (fn [flag]
        (= (vfn flag) vertex))
      (span-flags span))))

(defn get-pair-flags
  [^Span span, vertex, edge]

  (let [efn (edge-fn span)
        vfn (vertex-fn span)]
    (filter
      (fn [flag]
        (and
          (= (efn flag) edge)
          (= (vfn flag) vertex)))
      (span-flags span))))

; The incidence relations in this topos
(defn get-incident-vertices
  [^Span span, edge]

  (let [vfn (vertex-fn span)]
    (multiset
      (map
        (fn [flag]
          (vfn flag))
        (get-edge-flags span edge)))))

(defn get-incident-edges
  [^Span span, vertex]

  (let [efn (edge-fn span)]
    (multiset
      (map
        (fn [flag]
          (efn flag))
        (get-vertex-flags span vertex)))))

; Incidence structures are a lot like set systems
(defn vertex-system
  [^Span span]

  (multiset
    (map
      (fn [edge]
        (get-incident-vertices span edge))
      (span-edges span))))

(defn edge-system
  [^Span span]

  (multiset
    (map
      (fn [vertex]
        (get-incident-edges span vertex))
      (span-vertices span))))

; Degrees of vertices and edges in the span copresheaf topos
(defn span-edge-degree
  [^Span span, edge]

  (count (get-incident-vertices span edge)))

(defn span-vertex-degree
  [^Span span, vertex]

  (count (get-incident-edges span vertex)))

(defn empty-vertices
  [^Span span]

  (set
    (filter
      (fn [vertex]
        (zero? (span-vertex-degree span vertex)))
      (span-vertices span))))

(defn empty-edges
  [^Span span]

  (set
    (filter
      (fn [edge]
        (zero? (span-edge-degree span edge)))
      (span-edges span))))

; The incidence relation
(defn flag-pair
  [span flag]

  (list (edge-component span flag) (vertex-component span flag)))

(defn flag-pairs
  [span]

  (multiset
    (map
      (fn [i]
        (flag-pair span i))
      (span-flags span))))

(defn incidence-relation
  [span]

  (set (flag-pairs span)))

(defmethod underlying-relation Span
  [^Span span]

  (incidence-relation span))

(defmethod underlying-multirelation Span
  [^Span span]

  (flag-pairs span))

; Products and coproducts in the topos of span copresheaves
(defn span-product
  [& spans]

  (Span.
    (apply product (map span-flags spans))
    (apply product (map span-edges spans))
    (apply product (map span-vertices spans))
    (fn [coll]
      (map-indexed
        (fn [i flag]
          (edge-component (nth spans i) flag))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i flag]
          (vertex-component (nth spans i) flag))
        coll))))

(defn span-coproduct
  [& spans]

  (Span.
    (apply coproduct (map span-flags spans))
    (apply coproduct (map span-edges spans))
    (apply coproduct (map span-vertices spans))
    (fn [[i v]]
      (list i (edge-component (nth spans i) v)))
    (fn [[i v]]
      (list i (vertex-component (nth spans i) v)))))

(defmethod product Span
  [& args]

  (apply span-product args))

(defmethod coproduct Span
  [& args]

  (apply span-coproduct args))

; A simple span is one for which doesn't have any flags with equal decompositions
; In order to define this we of course use the traditional (edge,vertex) ordering
; of flag decompositions in the span topos.
(defn simple-span
  [edges vertices rel]

  (Span.
    rel
    edges
    vertices
    first
    second))

(defn family-span
  [edges]

  (let [vertices (dimembers edges)
        rel (seqable-binary-relation
              edges
              vertices
              (fn [[edge vertex]]
                (contains? edge vertex)))]
    (simple-span
      edges
      vertices
      rel)))

(defn multiplicity-relation
  [coll]

  (set
    (mapcat
     (fn [elem]
       (map
         (fn [i]
           (list elem i))
         (range (multiplicity coll elem))))
     (support coll))))

(defn multifamily-span
  [coll]

  (let [vertices (dimembers coll)
        edges (multiplicity-relation coll)
        rel (seqable-binary-relation
              edges
              vertices
              (fn [[[edge n] vertex]]
                (contains? edge vertex)))]
    (simple-span
      edges
      vertices
      rel)))

; Complex spans, meaning ones that are not simple, can have the property
; that a given pair of an incident vertex and an edge can occur more then
; once. These are an important part of the complete theory of the topos
; of span copresheaves.
(defn multiset-classifier
  [coll]

  (apply
    union
    (map
      (fn [elem]
        (set
          (map
           (fn [i]
             (list coll elem i))
           (range (multiplicity coll elem)))))
      (support coll))))

(defn clan-span
  [coll]

  (let [vertices (apply union (map set coll))]
    (->Span
      (apply union (map multiset-classifier coll))
      coll
      vertices
      first
      second)))

(defn multiclan-span
  [coll]

  (let [edges (multiplicity-relation coll)
        vertices (apply union (map set coll))]
    (->Span
      (apply
        union
        (map
         (fn [[edge n]]
           (apply
             union
             (map
               (fn [elem]
                 (set
                   (map
                    (fn [i]
                      (list (list edge n) elem i))
                    (range (multiplicity edge elem)))))
               (support edge))))
         edges))
      edges
      vertices
      first
      second)))

; example spans
(def exspan1
  (Span.
    #{0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15}
    #{0 1}
    #{0 1 2 3 4 5 6 7}
    (fn [i]
      (mod i 2))
    (fn [j]
      (int (/ j 2)))))

(def exspan2
  (Span.
    (cartesian-power #{0 1 2} 3)
    #{0 1 2}
    #{0 1 2}
    first
    second))

; Ontology of span copresheaves
(defn span?
  [object]

  (= (type object) Span))


