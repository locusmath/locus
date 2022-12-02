(ns locus.distance.lawvere.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all])
  (:import (locus.distance.lawvere.metric LawvereMetric)))

; Morphisms in the category of metric spaces
; Specifically if X and Y are metric spaces then f: X -> Y is a short map
; provided that for any two points x and y : d(f(x),f(y)) <= d(x,y)
; so that the distances between points are non-increasing by the function.
(deftype ShortMap [source target func]
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

(derive ShortMap :locus.base.logic.structure.protocols/structured-function)

; Identities and composition in the category Top
(defmethod identity-morphism LawvereMetric
  [metric]

  (ShortMap. metric metric identity))

(defmethod compose* ShortMap
  [a b]

  (ShortMap.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))




