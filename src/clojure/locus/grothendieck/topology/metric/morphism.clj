(ns locus.grothendieck.topology.metric.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.grothendieck.topology.metric.object :refer :all])
  (:import (locus.grothendieck.topology.metric.object MetricSpace)))

; Morphisms in the category of metric spaces
; Specifically if X and Y are metric spaces then f: X -> Y is a short map
; provided that for any two points x and y : d(f(x),f(y)) <= d(x,y)
; so that the distances between points are non increasing by the function.
(deftype ShortMap [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Identities and composition in the category Top
(defmethod identity-morphism MetricSpace
  [metric]

  (ShortMap. metric metric identity))

(defmethod compose* ShortMap
  [a b]

  (ShortMap.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))


