(ns locus.digraph.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]))

; Digraphs:
; Let F be a copresheaf, then F is naturally associated to a lattice of presheaves of digraphs
; Digraph(F) that have F as their underlying presheaf. This naturally generalises how sets
; can be associated to digraphs on them, only now we place directed graphs on presheaves
; instead of sets. For sets this reproduces ordinary digraphs, for functions this reproduces
; digraph homomorphisms, for bijections this reproduces digraph isomorphisms, etc. So digraphs
; are treated presheaf theoretically as special types of presheaves of directed graphs.

; An alternative treatment is possible using the topos of quivers, but the two aren't the same
; as you can have a digraph quiver. A digraph quiver is a presheaf of directed graphs whose
; underlying presheaf is a quiver. We distinguish between these two notions in order to
; deal with the different

(deftype SetDigraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive SetDigraph :locus.set.logic.structure.protocols/structured-set)

; Digraph constructors
(defn digraph
  [rel]

  (SetDigraph. (vertices rel) rel))

(defn empty-digraph
  [coll]

  (SetDigraph. coll #{}))

(defn full-digraph
  [coll]

  (SetDigraph. coll (complete-relation coll)))

; Get the underlying relations and multirelations of directed graphs
(defmethod underlying-relation SetDigraph
  [^SetDigraph digraph]

  (.-edges digraph))

(defmethod underlying-multirelation SetDigraph
  [^SetDigraph digraph]

  (underlying-relation digraph))

(defmethod visualize SetDigraph
  [^SetDigraph digraph] (visualize (underlying-relation digraph)))

; Conversion routines
(defmethod to-quiver SetDigraph
  [^SetDigraph digraph]

  (thin-quiver
    (underlying-set digraph)
    (underlying-relation digraph)))

; Convert various objects to directed graphs
(defmulti to-digraph type)

(defmethod to-digraph SetDigraph
  [digraph] digraph)

(defmethod to-digraph :locus.set.quiver.structure.core.protocols/thin-quiver
  [quiver]

  (SetDigraph. (objects quiver) (underlying-relation quiver)))

(defmethod to-digraph :locus.set.logic.core.set/universal
  [coll]

  (digraph coll))

(defmethod to-digraph :default
  [structure]

  (digraph (underlying-relation structure)))

; Digraph properties
(defn digraph-order
  [digraph]

  (count (underlying-set digraph)))

(defn digraph-size
  [digraph]

  (count (underlying-relation digraph)))

; Transformations of digraphs
(defn transpose-digraph
  [^SetDigraph digraph]

  (SetDigraph.
    (underlying-set digraph)
    (transpose (underlying-relation digraph))))

(defn complement-digraph
  [^SetDigraph digraph]

  (SetDigraph.
    (underlying-set digraph)
    (difference (complete-relation (underlying-set digraph)) (underlying-relation digraph))))

; In and out neighbours of digraph vertices
(defn out-neighbours
  [^SetDigraph digraph, x]

  (set
    (for [[a b] (underlying-relation digraph)
          :when (= a x)]
      b)))

(defn in-neighbours
  [^SetDigraph digraph, x]

  (set
    (for [[a b] (underlying-relation digraph)
          :when (= b x)]
      a)))

(defn sink-vertices
  [^SetDigraph digraph]

  (set
    (filter
      (fn [vertex]
        (empty? (out-neighbours digraph vertex)))
      (underlying-set digraph))))

(defn source-vertices
  [^SetDigraph digraph]

  (set
    (filter
      (fn [vertex]
        (empty? (in-neighbours digraph vertex)))
      (underlying-set digraph))))

(defn vertex-in-degree
  [^SetDigraph digraph, vertex]

  (count (in-neighbours digraph vertex)))

(defn vertex-out-degree
  [^SetDigraph digraph, vertex]

  (count (out-neighbours digraph vertex)))

(defn digraph-in-degree-sequence
  [^SetDigraph digraph]

  (map
    (fn [vertex]
      (vertex-in-degree digraph vertex))
    (underlying-set digraph)))

(defn digraph-out-degree-sequence
  [^SetDigraph digraph]

  (map
    (fn [vertex]
      (vertex-out-degree digraph vertex))
    (underlying-set digraph)))

; Condense the strongly connected components of the directed graph into single nodes
(defn digraph-weak-connectivity
  [digraph]

  (weak-connectivity (underlying-relation digraph)))

(defn digraph-strong-connectivity
  [digraph]

  (strong-connectivity (underlying-relation digraph)))

(defn condensation-digraph
  [digraph]

  (->SetDigraph
    (digraph-strong-connectivity digraph)
    (condensation (underlying-relation digraph))))

; Get subobjects of digraphs by restricting them
(defn restrict-digraph
  [digraph new-vertex-set]

  (->SetDigraph
    new-vertex-set
    (subrelation (underlying-relation digraph) new-vertex-set)))

; Product and coproducts of directed graphs
; The products and coproducts of directed graphs correspond to their products and coproducts as
; binary relations over a set.
(defmethod coproduct SetDigraph
  [& digraphs]

  (SetDigraph.
    (apply cartesian-coproduct (map underlying-set digraphs))
    (apply sum-relation (map underlying-relation digraphs))))

(defmethod product SetDigraph
  [& digraphs]

  (SetDigraph.
    (apply cartesian-product (map underlying-set digraphs))
    (apply product-relation (map underlying-relation digraphs))))

; The category of digraphs is defined by a special adjunction defined for any function between
; directed graph images and inverse images.
(defmethod image
  [:locus.set.logic.structure.protocols/set-function SetDigraph]
  [func digraph]

  (SetDigraph.
    (outputs func)
    (set
      (map
        (fn [[a b]]
          (list (func a) (func b)))
        (underlying-relation digraph)))))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function SetDigraph]
  [func digraph]

  (let [mapping (fiber-valued-mapping func)]
    (SetDigraph.
      (inputs func)
      (set
        (apply
          concat
          (map
            (fn [[a b]]
              (cartesian-product (get mapping a) (get mapping b)))
            (underlying-relation digraph)))))))

; Ontology of directed graphs
(defn digraph?
  [digraph]

  (= (type digraph) SetDigraph))

(defn left-total-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (equal-universals?
      (relation-domain (underlying-relation digraph))
      (underlying-set digraph))))

(defn right-total-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (equal-universals?
      (relation-codomain (underlying-relation digraph))
      (underlying-set digraph))))

(defn bitotal-digraph?
  [digraph]

  (and
    (left-total-digraph? digraph)
    (right-total-digraph? digraph)))

(defn reflexive-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (reflexive? (underlying-relation digraph))))

(defn transitive-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (transitive? (underlying-relation digraph))))

(defn irreflexive-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (irreflexive? (underlying-relation digraph))))

(defn antisymmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (antisymmetric-digraph? (underlying-relation digraph))))

(defn asymmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (asymmetric? (underlying-relation digraph))))

(defn symmetric-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (symmetric-binary-relation? (underlying-relation digraph))))

(defn directed-acyclic-graph?
  [digraph]

  (and
    (digraph? digraph)
    (acyclic-relation? (underlying-relation digraph))))

(defn strongly-connected-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (strongly-connected-relation? (underlying-relation digraph))))

(defn weakly-connected-digraph?
  [digraph]

  (and
    (digraph? digraph)
    (weakly-connected-relation? (underlying-relation digraph))))

