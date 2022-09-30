(ns locus.combinat.hypergraph.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.combinat.hypergraph.object :refer :all])
  (:import (locus.combinat.hypergraph.object Hypergraph)
           (locus.base.function.core.object SetFunction)))

;  Morphisms in the category of hypergraphs
(deftype HypergraphMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; The edge set of a hypergraph is a copresheaf valued field producing a functor
(defn morphism-of-edge-sets
  [morphism]

  (SetFunction.
    (edge-set (source-object morphism))
    (edge-set (target-object morphism))
    (fn [coll]
      (set-image (underlying-function morphism) coll))))

; Composition and identities of the category of hypergraphs
(defmethod compose* HypergraphMorphism
  [a b]

  (HypergraphMorphism. (source-object b) (target-object a) (comp (.func a) (.func b))))

(defmethod identity-morphism Hypergraph
  [hypergraph]

  (HypergraphMorphism. hypergraph hypergraph identity))

; Ontology of hypergraph homomorphisms
(defn hypergraph-homomorphism?
  [morphism]

  (= (type morphism) HypergraphMorphism))

(defn hypergraph-endomorphism?
  [morphism]

  (and
    (hypergraph-homomorphism? morphism)
    (= (source-object morphism) (target-object morphism))))

; Graph homomorphisms as special cases of hypergraph homomorphisms
(defn graph-homomorphism?
  [morphism]

  (and
    (hypergraph-homomorphism? morphism)
    (graph? (source-object morphism))
    (graph? (target-object morphism))))

(defn graph-endomorphism?
  [morphism]

  (and
    (graph-homomorphism? morphism)
    (= (source-object morphism) (target-object morphism))))

(defn simple-graph-homorphism?
  [morphism]

  (and
    (hypergraph-homomorphism? morphism)
    (simple-graph? (source-object morphism))
    (simple-graph? (target-object morphism))))
