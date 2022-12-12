(ns locus.set.copresheaf.quiver.permutable.element
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.quiver.binary.element.object :as qe]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.element.object QuiverObject QuiverMorphism)))

; Morphic elements of permutable quivers
(deftype PermutableQuiverMorphism [quiver morphism]
  Element
  (parent [this]
    quiver)

  SectionElement
  (tag [this] 0)
  (member [this] morphism)

  IdentifiableInstance
  (unwrap [this]
    (list (tag this) (member this)))

  Object
  (equals [this b]
    (and
      (instance? QuiverMorphism b)
      (= (.-quiver this) (.-quiver ^QuiverMorphism b))
      (= (.-morphism this) (.-morphism ^QuiverMorphism b))))

  Invertible
  (inv [this]
    (PermutableQuiverMorphism.
      quiver
     (invert-morphism quiver morphism)))

  AbstractMorphism
  (source-object [this]
    (QuiverObject. quiver (source-element quiver morphism)))
  (target-object [this]
    (QuiverObject. quiver (target-element quiver morphism))))

(derive PermutableQuiverMorphism :locus.set.logic.structure.protocols/element)

(defmethod wrap :locus.set.copresheaf.structure.core.protocols/structured-permutable-quiver
  [quiver [i v]]

  (cond
    (= i 0) (PermutableQuiverMorphism. quiver v)
    (= i 1) (QuiverObject. quiver v)))

; Ontology of permutable quiver morphisms
(defn permutable-quiver-morphism?
  [morphism]

  (= (type morphism) PermutableQuiverMorphism))

(defn permutable-quiver-involution-morphism?
  [morphism]

  (and
    (permutable-quiver-morphism? morphism)
    (let [quiv (parent morphism)
          i (member morphism)]
      (= (invert-morphism quiv i) i))))

