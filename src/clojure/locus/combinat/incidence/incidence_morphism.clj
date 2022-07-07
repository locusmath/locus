(ns locus.combinat.incidence.incidence-morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.combinat.hypergraph.object :refer :all]
            [locus.combinat.hypergraph.morphism :refer :all]
            [locus.combinat.incidence.incidence-structure :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)
           (locus.combinat.hypergraph.morphism HypergraphMorphism)
           (locus.combinat.incidence.incidence-structure IncidenceStructure)))

;  Morphisms in the category of incidence structures
(deftype IncidenceMorphism [source target f g]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] (SetFunction. (first-set source) (first-set target) f))
  (second-function [this] (SetFunction. (second-set source) (second-set target) f)))

; Conversion routines for morphisms in the category of incidence structures
; these produce part of the embedding of the category of hypergraphs within the category
; of incidence structures, which is in turn embedded in the span topos.
(defmulti to-incidence-morphism type)

(defmethod to-incidence-morphism IncidenceMorphism
  [morphism] morphism)

(defmethod to-incidence-morphism HypergraphMorphism
  [morphism]

  (let [func (underlying-function morphism)]
    (IncidenceMorphism.
     (to-incidence-structure (source-object morphism))
     (to-incidence-structure (target-object morphism))
     func
     (fn [line]
       (set-image func line)))))

; The flags forms a set valued functor on the category of incidence structures
(def morphism-of-points first-function)

(def morphism-of-lines second-function)

(defn morphism-of-flags
  [morphism]

  (SetFunction.
    (flags (source-object morphism))
    (flags (target-object morphism))
    (fn [[point line]]
      (list ((first-function morphism) point)
            ((second-function morphism) line)))))

; Identities and composition in the category of incidence structures
(defmethod compose* IncidenceMorphism
  [a b]

  (IncidenceMorphism.
    (source-object b)
    (target-object a)
    (comp (.f a) (.f b))
    (comp (.g a) (.g b))))

(defmethod identity-morphism IncidenceStructure
  [structure]

  (IncidenceMorphism.
    structure
    structure
    identity
    identity))
