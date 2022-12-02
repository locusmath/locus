(ns locus.order.general.core.isomorphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.invertible.function.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.vertexset :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; A preorder isomorphism, as a presheaf of preorders, is a functor F: K_2 -> Ord. Instead
; of the base category T_2, it uses the index groupoid K_2 which ensures that each
; of its monotone maps must have inverse. An isomorphism of preorders can be described
; by a pair of monotone maps F: A -> B and G: B -> A such that the composition of these
; two monotone maps is the identity in both directions. Isomorphisms of preorders
; are also special types of Galois connections. In particular, they are the Galois
; connections in which both the closure and the dual closure operations on A and B
; are trivial.
(deftype PreorderIsomorphism [source target forwards backwards]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction (morphisms source) (morphisms target) (partial map forwards)))
  (second-function [this]
    (->SetFunction (objects source) (objects target) forwards))

  Invertible
  (inv [this]
    (PreorderIsomorphism.
      target
      source
      backwards
      forwards))

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (forwards arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Isomorphisms of preorders are monotone maps
(derive PreorderIsomorphism :locus.elementary.copresheaf.core.protocols/monotone-map)

; The groupoid of preorders is a special type of category, so every preorder object has an
; associated identity morphism. That identity morphism is implemented here. Together with
; the composition operation, this makes up our implementation of the groupoid of preorders,
; which is a wide subcategory of the category of preorders and monotone maps.
(defn identity-order-isomorphsim
  [preorder]

  (->PreorderIsomorphism
    preorder
    preorder
    identity
    identity))

; Isomorphisms of preorders are morphisms in the groupoid of preorders. As morphisms in a category
; they are composable. That composition operation is implemented here.
(defmethod compose* PreorderIsomorphism
  [^PreorderIsomorphism a, ^PreorderIsomorphism b]

  (->PreorderIsomorphism
    (source-object b)
    (target-object a)
    (compose (.-forwards a) (.-forwards b))
    (compose (.-backwards b) (.-backwards a))))

; Create a discrete preorder isomorphism from an invertible function
(defn discrete-preorder-isomorphism
  [func]

  (->PreorderIsomorphism
    (discrete-preorder (inputs func))
    (discrete-preorder (outputs func))
    (underlying-function func)
    (underlying-function (inv func))))

; Convert a preorder-isomorphism into an invertible function by getting its underlying presheaf
(defmethod to-invertible-function PreorderIsomorphism
  [^PreorderIsomorphism preorder-isomorphism]

  (->InvertibleFunction
    (inputs preorder-isomorphism)
    (outputs preorder-isomorphism)
    (.-forwards preorder-isomorphism)
    (.-backwards preorder-isomorphism)))

; Ontology of preorder isomorphisms
(defn preorder-isomorphism?
  [obj]

  (= (type obj) PreorderIsomorphism))