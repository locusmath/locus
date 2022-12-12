(ns locus.set.quiver.binary.thin.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

; A quiver is considered to be a thin quiver, provided that in each hom class of the
; quiver there is at most one object. This naturally generalises the idea of a
; thin category to quivers.

; Thin quivers
(deftype ThinQuiver [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices)

  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] this)
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e))

(derive ThinQuiver :locus.set.quiver.structure.core.protocols/thin-quiver)

; Create a thin quiver
(defn thin-quiver
  ([edges]
   (ThinQuiver. (vertices edges) edges))

  ([vertices edges]
  (ThinQuiver. vertices edges)))

(defn thin-quiver-component
  [quiver]

  (ThinQuiver.
    (objects quiver)
    (underlying-relation quiver)))

; Multimethods
(defmethod underlying-relation ThinQuiver
  [quiv] (morphisms quiv))

(defmethod underlying-multirelation ThinQuiver
  [quiv] (morphisms quiv))

(defmethod visualize ThinQuiver
  [quiv] (visualize (underlying-relation quiv)))

; Transposition of thin quivers
(defmethod dual ThinQuiver
  [^ThinQuiver quiv] (->ThinQuiver (.-vertices quiv) (transpose (.-edges quiv))))
