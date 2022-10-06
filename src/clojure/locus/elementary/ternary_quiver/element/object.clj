(ns locus.elementary.ternary-quiver.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]))

; If the topos of ternary quivers is considered as a concrete category, then its elements are precisely
; the objects and morphisms of the ternary quiver.
(deftype TernaryQuiverObject [quiver object]
  Element
  (parent [this]
    quiver)

  SectionElement
  (tag [this] 1)
  (member [this] object)

  Object
  (equals [this b]
    (and
      (instance? TernaryQuiverObject b)
      (= quiver (.-quiver ^TernaryQuiverObject b))
      (= object (.-object ^TernaryQuiverObject b))))

  IdentifiableInstance
  (unwrap [this]
    (list (tag this) (member this))))

(deftype TernaryQuiverMorphism [quiver morphism]
  Element
  (parent [this]
    quiver)

  SectionElement
  (tag [this] 0)
  (member [this] morphism)

  Object
  (equals [this b]
    (and
      (instance? TernaryQuiverMorphism b)
      (= quiver (.-quiver ^TernaryQuiverMorphism b))
      (= morphism (.-morphism ^TernaryQuiverMorphism b))))

  IdentifiableInstance
  (unwrap [this]
    (list (tag this) (member this))))

(derive TernaryQuiverObject :locus.base.logic.structure.protocols/element)
(derive TernaryQuiverMorphism :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiv [i v]]

  (cond
    (= i 0) (->TernaryQuiverMorphism quiv v)
    (= i 1) (->TernaryQuiverObject quiv v)))

; Elements of ternary quivers
(defn ternary-quiver-element?
  [elem]

  (or
    (= (type elem) TernaryQuiverObject)
    (= (type elem) TernaryQuiverMorphism)))

(defn ternary-quiver-object?
  [elem]

  (= (type elem) TernaryQuiverObject))

(defn ternary-quiver-morphism?
  [elem]

  (= (type elem) TernaryQuiverMorphism))