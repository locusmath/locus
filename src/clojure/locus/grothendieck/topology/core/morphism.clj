(ns locus.grothendieck.topology.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.grothendieck.topology.core.object :refer :all])
  (:import (locus.grothendieck.topology.core.object TopologicalSpace)))

; We say that a map of topological spaces f: X -> Y is a continuous map
; provided that f reflects all open sets in Y. Then the composition of
; continuous maps is again continuous, so they form morphisms in the category
; Top of topological spaces and continuous maps.
(deftype ContinuousMap [in out func]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  ConcreteMorphism
  (inputs [this] (underlying-set in))
  (outputs [this] (underlying-set out))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Identities and composition in the category Top
(defmethod identity-morphism TopologicalSpace
  [topology]

  (ContinuousMap. topology topology identity))

(defmethod compose* ContinuousMap
  [a b]

  (ContinuousMap.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; Ontology of continuous maps
(defn continuous-map?
  [morphism]

  (= (type morphism) ContinuousMap))