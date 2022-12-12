(ns locus.order.meet-semilattice.core.morphism
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
            [locus.order.meet-semilattice.core.object :refer :all])
  (:import (locus.order.meet_semilattice.core.object MeetSemilattice)))

; The category of meet semilattices is a subcategory of the category of thin categories. Meet
; semilattices are the thin categories that have all finite products, so their morphisms
; are simply the functors between them that preserve all products. There are functors
; of meet semilattices that don't preserve products, these don't belong to this category.
; There is a functor from meet semilattices to the category of semigroups which gives
; this category its special flavour.
(deftype MorphismOfMeetSemilattices [source target func]
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

(derive MorphismOfMeetSemilattices :locus.set.copresheaf.structure.core.protocols/monotone-map)

; Composition and identities of join categories
(defmethod identity-morphism MeetSemilattice
  [obj] (MorphismOfMeetSemilattices obj obj identity))

(defmethod compose* MorphismOfMeetSemilattices
  [a b]

  (MorphismOfMeetSemilattices
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))