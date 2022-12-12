(ns locus.digraph.mapping.function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.quiver.binary.thin.morphism :refer :all]
            [locus.set.quiver.binary.thin.morphism :refer :all]
            [locus.digraph.core.object :refer :all]))

; Let F be a presheaf, then Digraph(F) is its lattice of directed graphs. Digraph(F) consists
; of all structure presheaves of digraphs that have F as their underlying presheaf. In the
; special case of a function F: A -> B between two sets, this reproduces a homomorphism
; of directed graphs, which is a presheaf of directed graphs over the ordered pair category.
; In general, directed graphs can be handled by presheaves over various index categories.

(deftype DigraphFunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive DigraphFunction :locus.set.logic.structure.protocols/structured-function)

; Morphisms of directed edge sets of digraphs form a functor to the topos of sets
(defn morphism-of-directed-edge-sets
  [morphism]

  (SetFunction.
    (underlying-relation (source-object morphism))
    (underlying-relation (target-object morphism))
    (fn [[a b]]
      (list (morphism a) (morphism b)))))

; Composition and identities of the category of directed graphs
(defmethod compose* DigraphFunction
  [a b]

  (DigraphFunction
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism DigraphFunction
  [digraph]

  (DigraphFunction
    digraph
    digraph
    identity))

; Convert various structures into homomorphisms of directed graphs
(defmulti to-digraph-function type)

(defmethod to-digraph-function DigraphFunction
  [func] func)

(defmethod to-digraph-function :locus.set.logic.structure.protocols/set-function
  [func]

  (->DigraphFunction
    (empty-digraph (source-object func))
    (empty-digraph (target-object func))
    func))

; There is a functor from digraphs to quivers, which turns them in to a different kind of functor
(defmethod to-morphism-of-quivers DigraphFunction
  [^DigraphFunction func]

  (->MorphismOfThinQuivers
    (to-quiver (source-object func))
    (to-quiver (target-object func))
    (.-func func)))

; Ontology of functions of digraphs
(defn digraph-function?
  [obj]

  (= (type obj) DigraphFunction))