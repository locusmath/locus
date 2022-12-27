(ns locus.lawvere.metric.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.lawvere.metric.core.object :refer :all])
  (:import (locus.lawvere.metric.core.object LawvereMetric)))

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

(derive ShortMap :locus.set.logic.structure.protocols/structured-function)

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




