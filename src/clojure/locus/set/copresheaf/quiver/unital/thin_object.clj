(ns locus.set.copresheaf.quiver.unital.thin-object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

; A unital quiver is said to be thin provided that for each hom class Hom(A,B) for each pair of
; objects A and B in the quiver Q, the hom class contains no more than one element. In that case,
; the unital quiver can be described entirely by a relation. The identity element is the
; equal ordered pair containing a vertex.

(deftype ThinUnitalQuiver [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices)

  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  StructuredQuiver
  (underlying-quiver [this] this)
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] this)
  (identity-morphism-of [this obj] (list obj obj)))

(derive ThinUnitalQuiver :locus.set.copresheaf.quiver.unital.object/unital-quiver)

; Create thin unital quivers
(defn thin-unital-quiver
  ([rel]
   (thin-unital-quiver (vertices rel) rel))
  ([vertices rel]
   (->ThinUnitalQuiver vertices rel)))

; Underlying relations of thin quivers are easier to access and understand
(defmethod underlying-relation ThinUnitalQuiver
  [^ThinUnitalQuiver quiver] (.-edges quiver))

(defmethod underlying-multirelation ThinUnitalQuiver
  [^ThinUnitalQuiver quiver] (.-edges quiver))

(defmethod visualize ThinUnitalQuiver
  [^ThinUnitalQuiver quiver] (visualize (.-edges quiver)))

; Duls of thin unital quivers
(defmethod dual ThinUnitalQuiver
  [quiver] (->ThinQuiver (.-vertices quiver) (transpose (.-edges quiver))))