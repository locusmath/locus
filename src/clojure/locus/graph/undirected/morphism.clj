(ns locus.graph.undirected.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.hypergraph.core.object :refer :all]
            [locus.hypergraph.core.morphism :refer :all])
  (:import (locus.hypergraph.core.morphism HypergraphMorphism)))

; Identities in the category of graphs
(defmethod identity-morphism Graph
  [graph]

  (HypergraphMorphism graph graph identity))


