(ns locus.structure.general.functor
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.concrete.concrete-category :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.algebra.category.concrete.categories :refer :all]))

; A copresheaf is a set-valued functor F: C -> Sets. This concept is suitable for a great many
; purposes. However, quite often we would prefer instead to define functors into concrete
; categories rather then Sets. Then we get a chain of functors F: C -> D -> Sets, in which
; F has an underlying copresheaf by composition F: C -> Sets as well as an underlying
; functor F: C -> D. These are the structure copresheaves, which can be handled here. In
; order to deal with the difference between the map to D and to Sets we have different
; multimethods that deal with separately with both types of functor.

(deftype StructureCopresheaf [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive StructureCopresheaf :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Structure copresheaves have underlying functors
(defmethod get-object StructureCopresheaf
  [copresheaf x]

  ((second-function copresheaf) x))

(defmethod get-morphism StructureCopresheaf
  [copresheaf x]

  ((first-function copresheaf) x))

; Structure copresheaves have underlying copresheaves
(defmethod get-set StructureCopresheaf
  [copresheaf x]

  (let [target (target-object copresheaf)
        obj (get-object copresheaf x)]
    (object-to-set target obj)))

(defmethod get-function StructureCopresheaf
  [copresheaf x]

  (let [target (target-object copresheaf)
        arrow (get-morphism copresheaf x)]
    (morphism-to-function target arrow)))

; Structure copresheaves can be converted back into ordinary functors
(defmethod to-functor StructureCopresheaf
  [copresheaf]

  (->Functor
    (source-object copresheaf)
    (target-object copresheaf)
    (partial get-object copresheaf)
    (partial get-morphism copresheaf)))

; Conversion routines for copresheaves of structures
(defmulti to-structure-copresheaf type)

(defmethod to-structure-copresheaf StructureCopresheaf
  [structure-copresheaf] structure-copresheaf)

; Ontology of structure copresheaves
(defmulti structure-copresheaf? type)

(defmethod structure-copresheaf? :locus.set.copresheaf.structure.core.protocols/structure-copresheaf
  [copresheaf] true)

(defmethod structure-copresheaf? :default
  [func] false)