(ns locus.combinat.incidence.incidence-morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.combinat.hypergraph.object :refer :all]
            [locus.combinat.hypergraph.morphism :refer :all]
            [locus.combinat.incidence.incidence-structure :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.combinat.hypergraph.morphism HypergraphMorphism)
           (locus.combinat.incidence.incidence_structure IncidenceStructure)))

; Morphisms in the category of incidence structures
; The category of incidence structures is associated to a faithful functor to the topos Sets^2,
; so a morphism of incidence structures can be treated as a special case of a morphism
; in Sets^2 with extra structure.
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
