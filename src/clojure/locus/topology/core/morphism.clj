(ns locus.topology.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.topology.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all])
  (:import (locus.topology.core.object TopologicalSpace)))

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

; Topological images and inverse images form an adjoint relationship in topology
(defn topological-image
  [function source-topology]

  (let [output-opens (set
                       (filter
                         (fn [out-set]
                           (contains? (.-opens source-topology) (set-inverse-image function out-set)))
                         (power-set (outputs function))))]
    (->TopologicalSpace
      (outputs function)
      output-opens)))

(defn topological-inverse-image
   [function target-topology]

  (let [input-opens (set
                      (map
                        (fn [out-set]
                          (set-inverse-image function out-set))
                        (.-opens target-topology)))]
    (->TopologicalSpace
      (inputs function)
      input-opens)))

(defmethod image
  [:locus.set.logic.structure.protocols/set-function
   :locus.grothendieck.topology.core.object/topology]
  [func topology]

  (topological-image func topology))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function
   :locus.grothendieck.topology.core.object/topology]
  [func topology]

  (topological-inverse-image func topology))

; The adjoint relationship between order and topology
(defn specialization-monotone-map
  [continuous-map]

  (->MonotoneMap
    (specialization-preorder (source-object continuous-map))
    (specialization-preorder (target-object continuous-map))
    (fn [i]
      (continuous-map i))))

(defn alexandrov-continuous-function
  [monotone-map]

  (->ContinuousMap
    (alexandrov-topology (source-object monotone-map))
    (alexandrov-topology (target-object monotone-map))
    (fn [i]
      (monotone-map i))))

; Ontology of continuous maps
(defn continuous-map?
  [morphism]

  (= (type morphism) ContinuousMap))
