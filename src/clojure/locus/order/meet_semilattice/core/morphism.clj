(ns locus.order.meet-semilattice.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
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

(derive MorphismOfMeetSemilattices :locus.elementary.copresheaf.core.protocols/monotone-map)

; Composition and identities of join categories
(defmethod identity-morphism MeetSemilattice
  [obj] (MorphismOfMeetSemilattices obj obj identity))

(defmethod compose* MorphismOfMeetSemilattices
  [a b]

  (MorphismOfMeetSemilattices
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))