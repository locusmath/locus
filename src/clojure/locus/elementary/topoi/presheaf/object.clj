(ns locus.elementary.topoi.presheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.preorder.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.contravariant-functor :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)))

; A presheaf is a contravariant functor F: C -> Sets. It is the dual concept to a copresheaf which
; is simply a covariant functor F: C -> Sets. The two concepts are essentially interchangeable
; as long as you switch the order of the elements of the index category.

(deftype Presheaf [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] (dual category))
  (target-object [this] sets)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

; Get the sets ond objects of a presheaf
(defmethod get-set Presheaf
  [presheaf x]

  ((second-function presheaf) x))

(defmethod get-function Presheaf
  [presheaf x]

  ((first-function presheaf) x))

; The index of a presheaf is the dual of its input category
(defmethod index Presheaf
  [^Presheaf presheaf]

  (dual (.category presheaf)))

; Conversion routines
(defmethod to-contravariant-functor Presheaf
  [^Presheaf presheaf]

  (->ContravariantFunctor
    (.category presheaf)
    sets
    (.-morphism_function presheaf)
    (.-object_function presheaf)))

; Presheaves and copresheaves are now considered to be dual concepts
(defmethod dual Presheaf
  [presheaf]

  (->Copresheaf
    (dual (.-category presheaf))
    (.-object_function presheaf)
    (.-morphism_function presheaf)))

(defmethod dual Copresheaf
  [^Copresheaf copresheaf]

  (->Presheaf
    (dual (.-category copresheaf))
    (.-object_function copresheaf)
    (.-morphism_function copresheaf)))

; Conversion routines for presheaves
(defmulti to-presheaf type)

(defmethod to-presheaf Presheaf
  [presheaf] presheaf)

(defmethod to-presheaf :default
  [obj] (dual (to-copresheaf obj)))

; Ontology of presheaves
(defn presheaf?
  [x]

  (= (type x) Presheaf))
