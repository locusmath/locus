(ns locus.graph.directed.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]))

;  Morphisms in the category of directed graphs
(deftype DigraphMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Morphisms of directed edge sets of digraphs form a functor to the topos of sets
(defn morphism-of-directed-edge-sets
  [morphism]

  (SetFunction.
    (underlying-relation (source-object morphism))
    (underlying-relation (target-object morphism))
    (fn [[a b]]
      (list (morphism a) (morphism b)))))

; Composition and identities of the category of directed graphs
(defmethod compose* DigraphMorphism
  [a b]

  (DigraphMorphism (source-object b) (target-object a) (comp (.func a) (.func b))))

(defmethod identity-morphism Digraph
  [digraph]

  (DigraphMorphism digraph digraph identity))


