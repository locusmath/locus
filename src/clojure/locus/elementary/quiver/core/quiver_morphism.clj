(ns locus.elementary.quiver.core.quiver-morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.quiver-object :refer :all])
  (:import (locus.elementary.quiver.core.quiver_object QuiverObject)))

; A quiver morphism is a generalisation of the idea of a morphism of a category,
; defined by losing information on composition. Morphisms of quivers still have
; source and target objects, but they are not composable. The QuiverMorphism class
; is therefore an implementor of the AbstractMorphism protocol.

(deftype QuiverMorphism [quiver morphism]
  AbstractMorphism
  (source-object [this]
    (QuiverObject. quiver (source-element quiver morphism)))
  (target-object [this]
    (QuiverObject. quiver (target-element quiver morphism))))

(defn quiver-morphisms
  [quiver]

  (set
    (map
      (fn [morphism]
        (QuiverMorphism. quiver morphism))
      (morphisms quiver))))

; Ontology of quiver morphisms
(defn quiver-morphism?
  [morphism]

  (= (type morphism) QuiverMorphism))

(defn quiver-endomorphism?
  [morphism]

  (and
    (quiver-morphism? morphism)
    (= (source-object morphism) (target-object morphism))))