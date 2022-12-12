(ns locus.graph.mapping.function
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
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.quiver.binary.thin.morphism :refer :all]
            [locus.graph.core.object :refer :all])
  (:import (locus.graph.core.object SetGraph)))

; Let F be a presheaf then Graphs(F) is its lattice of presheaves of graphs. In the special case
; of a function, this produces the lattice of graph homomorphisms with a given underlying
; function. We can therefore speak of graph homomorphisms as being the structure of a graph
; on a given function, instead of them just being a morphism between graphs in the other
; direction. This means that graph homomorphisms are presheaves of graphs over the ordered
; pair category.

(deftype GraphFunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive GraphFunction :locus.set.logic.structure.protocols/structured-function)

; Composition and identities of the category of graphs
(defmethod compose* GraphFunction
  [a b]

  (GraphFunction.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism SetGraph
  [graph]

  (GraphFunction.
    graph
    graph
    identity))

; Conversion routines for homomorphisms of graphs
(defmulti to-graph-function type)

(defmethod to-graph-function GraphFunction
  [^GraphFunction func] func)

(defmethod to-graph-function :locus.set.logic.structure.protocols/set-function
  [func]

  (->GraphFunction
    (empty-graph (inputs func))
    (empty-graph (outputs func))
    func))

; Map graph homomorphisms into the topos of quivers
(defmethod to-morphism-of-quivers GraphFunction
  [^GraphFunction func]

  (->MorphismOfThinQuivers
    (to-quiver (source-object func))
    (to-quiver (target-object func))
    (.-func func)))

; Ontology of homomorphisms of graphs
(defn graph-function?
  [obj]

  (= (type obj) GraphFunction))