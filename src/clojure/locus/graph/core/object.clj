(ns locus.graph.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]))

; Graphs:
; Let F be a presheaf, then F is naturally associated to a lattice of presheaves of graphs that
; have F as their underlying presheaf which we can call Graph(F). This generalises the idea
; of a graph on a set to a graph on a presheaf. In the case of a set this returns an ordinary
; graph, in the case of a function this produces a graph homomorphism, and in general this
; produces a homomorphism of graphs. In accordance with presheaf theoretic foundations, everything
; is interpreted in terms of presheaves instead of sets.

; In presheaf topos theory, graphs can be understood by permutable quivers which are quivers
; with a single symmetric operation on their morphism set. Then graphs are simply the subcategory
; of the topos of permutable quivers consisting of thin permutable quivers. We distinguish between
; graphs and quivers so that we consider presheaves of graphs, while quivers are just certain
; presheaves of sets that can recover the data of graphs.

(deftype SetGraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive SetGraph :locus.elementary.function.core.protocols/structured-set)

; Properties of graphs
(defn graph-edges
  [^SetGraph graph]

  (.-edges graph))

(defn nonloop-graph-edges
  [^SetGraph graph]

  (set
    (filter
      (fn [edge]
        (not= (count edge) 1))
      (graph-edges graph))))

(defn loop-graph-edges
  [^SetGraph graph]

  (set
    (filter
      (fn [edge]
        (= (count edge) 1))
      (graph-edges graph))))

; Irreflexive interior and reflexive closure for graphs
(defn irreflexive-component-graph
  [graph]

  (->SetGraph
    (underlying-set graph)
    (nonloop-graph-edges graph)))

(defn reflexive-closure-graph
  [graph]

  (let [coll (underlying-set graph)]
    (->SetGraph
      coll
     (union
       (set
         (map
           (fn [i]
             #{i})
           coll))))))

; Underlying relations, multirelations, and visualisations of graphs
(defmethod underlying-relation SetGraph
  [^SetGraph graph]

  (apply
    union
    (map
      (fn [pair]
        (if (= (count pair) 1)
          (let [[a] (seq pair)]
            #{(list a a)})
          (let [[a b] (seq pair)]
            #{(list a b) (list b a)})))
      (graph-edges graph))))

(defmethod underlying-multirelation SetGraph
  [^SetGraph graph] (multiset (underlying-relation graph)))

(defmethod visualize SetGraph
  [^SetGraph graph] (visualize (graph-edges graph)))

; Map graphs into the topos of quivers
(defmethod to-quiver SetGraph
  [^SetGraph graph]

  (->ThinQuiver
    (underlying-set graph)
    (underlying-relation graph)))

; Conversion routines for undirected graphs
(defmulti to-graph type)

(defmethod to-graph SetGraph
  [^SetGraph graph] graph)

(defmethod to-graph :locus.set.logic.core.set/universal
  [family]

  (->SetGraph (apply union family) family))

; Graph order and size metrics
(defn graph-order
  [graph]

  (count (underlying-set graph)))

(defn graph-size
  [graph]

  (count (graph-edges graph)))

; Implementation of complementation for the different types of graph
(defn complement-graph
  [graph]

  (SetGraph.
    (underlying-set graph)
    (difference
      (multiselection (underlying-set graph) #{1 2})
      (graph-edges graph))))

(defn complement-simple-graph
  [graph]

  (SetGraph.
    (underlying-set graph)
    (difference (selections (underlying-set graph) 2) (graph-edges graph))))

; Get the neighbours of an element of an undirected graph
(defn containing-edges
  [graph x]

  (set
    (filter
      (fn [edge]
        (contains? edge x))
      (graph-edges graph))))

(defn undirected-neighbours
  [graph x]

  (conj
    (apply
      union
      (filter
        (fn [edge]
          (contains? edge x))
        (graph-edges graph)))
    x))

; Construct a graph from a set system
(defn graph
  ([family]
   (graph (apply union family) family))
  ([coll family]
   (->SetGraph coll family)))

(defn empty-graph
  [coll]

  (->SetGraph coll #{}))

(defn complete-graph
  [coll]

  (->SetGraph
    coll
    (multiselection coll #{1 2})))

(defn complete-simple-graph
  [coll]

  (->SetGraph
    coll
    (selections coll 2)))

(defn cycle-graph
  [coll]

  (cond
    (<= (count coll) 1) (empty-graph coll)
    (= (count coll) 2) (SetGraph. (set coll) #{(set coll)})
    :else (->SetGraph
            (set coll)
            (set
              (map
                (fn [i]
                  (if (= i (dec (count coll)))
                    #{(nth coll i) (nth coll 0)}
                    #{(nth coll i) (nth coll (inc i))}))
                (range (count coll)))))))

(defn path-graph
  [coll]

  (->SetGraph
    (set coll)
    (map
      (fn [i]
        #{i (inc i)})
      (if (empty? coll)
        '()
        (range (dec (count coll)))))))

(defn star-graph
  [coll elem]

  (->SetGraph
    (conj coll elem)
    (set
      (map
        (fn [i]
          #{i elem})
        coll))))

(defn line-graph
  [graph]

  (SetGraph.
    (graph-edges graph)
    (set
      (for [[a b] (cartesian-power (graph-edges graph) 2)
            :when (not (empty? (intersection a b)))]
        #{a b}))))

(defn johnson-graph
  [coll k]

  (let [elems (selections coll k)]
    (SetGraph.
      elems
      (set
        (filter
          (fn [pair]
            (= (count (apply intersection pair)) (dec k)))
          (selections elems 2))))))

(defn kneser-graph
  [coll k]

  (let [elems (selections coll k)]
    (SetGraph.
      elems
      (set
        (filter
          (fn [pair]
            (empty? (apply intersection pair)))
          (selections elems 2))))))

; The category of graphs is defined by a fundamental adjunction that is produced for each function
; which is defined by graph images and inverse images.
(defmethod image
  [:locus.set.logic.structure.protocols/set-function SetGraph]
  [func graph]

  (->SetGraph
    (outputs func)
    (set
      (map
        (fn [edge]
          (set (map func edge)))
        (graph-edges graph)))))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function SetGraph]
  [func graph]

  (let [in (inputs func)
        edges (graph-edges graph)]
    (->SetGraph
      in
      (set
        (filter
          (fn [edge]
            (let [produced-edge (set (map func edge))]
              (contains? edges produced-edge)))
          (multiselection in #{1 2}))))))

; Create a restricted version of an undirected graph
(defn restrict-graph
  [graph new-vertex-set]

  (->SetGraph
    new-vertex-set
    (set
      (filter
        (fn [edge]
          (superset? (list edge new-vertex-set)))
        (graph-edges graph)))))

; Ontology of graphs
(defn graph?
  [obj]

  (= (type obj) SetGraph))

(defn simple-graph?
  [obj]

  (and
    (graph? obj)
    (empty? (loop-graph-edges graph))))

(defn empty-graph?
  [obj]

  (and
    (graph? obj)
    (empty? (graph-edges obj))))




