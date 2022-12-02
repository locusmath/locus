(ns locus.elementary.quiver.unital.thin-object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.thin.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.quiver.binary.core.object Quiver)))

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

(derive ThinUnitalQuiver :locus.elementary.quiver.unital.object/unital-quiver)

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