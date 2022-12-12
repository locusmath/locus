(ns locus.algebra.groupoid.element.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.groupoid.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.category.element.object CategoryObject)
           (locus.algebra.groupoid.core.object Groupoid)))

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

(derive GroupoidMorphism :locus.set.logic.structure.protocols/element)

(defmethod wrap :locus.set.copresheaf.structure.core.protocols/groupoid
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