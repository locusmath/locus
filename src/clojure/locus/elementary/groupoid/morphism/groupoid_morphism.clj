(ns locus.elementary.groupoid.morphism.groupoid-morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.object.category-object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.groupoid.core.object :refer :all])
  (:import (locus.elementary.category.object.category_object CategoryObject)
           (locus.elementary.groupoid.core.object Groupoid)))

; Morphisms in a groupoid
; The difference between morphisms in a groupoid and morphisms in a more general
; category is that groupoid morphisms always implement the invertible interface,
; which takes a morphism in a groupoid to its corresponding inverse.
(deftype GroupoidMorphism [groupoid morphism]
  AbstractMorphism
  (source-object [this]
    (CategoryObject. groupoid (source-element groupoid morphism)))
  (target-object [this]
    (CategoryObject. groupoid (target-element groupoid morphism)))

  Invertible
  (inv [this]
    (GroupoidMorphism. groupoid (invert-morphism groupoid morphism))))

; Composobality of groupoid morphisms
(defmethod compose* GroupoidMorphism
  [a b]

  (let [^Groupoid groupoid (.groupoid a)]
    (->GroupoidMorphism
      groupoid
        ((.func groupoid) (list (.morphism a) (.morphism b))))))