(ns locus.graph.undirected.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.hypergraph.core.object :refer :all]
            [locus.hypergraph.core.morphism :refer :all]))

;  Morphisms in the category of graphs
(deftype GraphMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Composition and identities of the category of graphs
(defmethod compose* GraphMorphism
  [a b]

  (GraphMorphism. (source-object b) (target-object a) (comp (.func a) (.func b))))

(defmethod identity-morphism Graph
  [graph]

  (GraphMorphism. graph graph identity))


