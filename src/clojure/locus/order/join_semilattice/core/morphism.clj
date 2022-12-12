(ns locus.order.join-semilattice.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.order.join-semilattice.core.object :refer :all])
  (:import (locus.order.join_semilattice.core.object JoinSemilattice)))

; The category of join semilattices is a subcategory of the category Ord of thin categories
; and monotone maps. There is a naturally defined functor from this category of semilattices
; to the category of semigroups.
(deftype MorphismOfJoinSemilattices [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this]
    (->SetFunction (morphisms source) (morphisms target) (partial map func)))
  (second-function [this]
    (->SetFunction (objects source) (objects target) func))

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Ontology of homomorphisms in the category of join semilattices
(derive MorphismOfJoinSemilattices :locus.set.copresheaf.structure.core.protocols/monotone-map)

; Composition and identities of join categories
(defmethod identity-morphism JoinSemilattice
  [obj] (MorphismOfJoinSemilattices. obj obj identity))

(defmethod compose* MorphismOfJoinSemilattices
  [a b]

  (MorphismOfJoinSemilattices.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))