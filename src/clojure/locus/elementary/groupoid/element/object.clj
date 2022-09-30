(ns locus.elementary.groupoid.element.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.element.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.groupoid.core.object :refer :all])
  (:import (locus.elementary.category.element.object CategoryObject)
           (locus.elementary.groupoid.core.object Groupoid)))

; Morphisms in a groupoid
; The difference between morphisms in a groupoid and morphisms in a more general
; category is that groupoid morphisms always implement the invertible interface,
; which takes a morphism in a groupoid to its corresponding inverse.
(deftype GroupoidMorphism [groupoid morphism]
  Element
  (parent [this] groupoid)

  SectionElement
  (tag [this] 0)
  (member [this] morphism)

  IdentifiableInstance
  (unwrap [this] (list (tag this) (member this)))

  AbstractMorphism
  (source-object [this]
    (CategoryObject. groupoid (source-element groupoid morphism)))
  (target-object [this]
    (CategoryObject. groupoid (target-element groupoid morphism)))

  Invertible
  (inv [this]
    (GroupoidMorphism. groupoid (invert-morphism groupoid morphism))))

(derive GroupoidMorphism :locus.base.logic.structure.protocols/element)

(defmethod wrap :locus.elementary.copresheaf.core.protocols/groupoid
  [groupoid [i v]]

  (cond
    (= i 0) (GroupoidMorphism. groupoid v)
    (= i 1) (CategoryObject. groupoid v)))

; Composobality of groupoid morphisms
(defmethod compose* GroupoidMorphism
  [a b]

  (let [^Groupoid groupoid (.groupoid a)]
    (->GroupoidMorphism
      groupoid
      ((.func groupoid) (list (.morphism a) (.morphism b))))))

; Ontology of morphism elements of groupoids
(defn groupoid-morphism?
  [element]

  (= (type element) GroupoidMorphism))