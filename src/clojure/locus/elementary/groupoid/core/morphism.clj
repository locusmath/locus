(ns locus.elementary.groupoid.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.groupoid.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)
           (locus.elementary.groupoid.core.object Groupoid)))

; Morphisms in the category of groupoids
; unlike for the functors of other categories, the functors in the category of groupoids
; must also preserve identities so that F(m^(-1)) = F(m)^(-1). It follows that every
; morphism of groupoids has an underlying morphism of dependency quivers.

(deftype GroupoidFunctor [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      (underlying-quiver source)
      (underlying-quiver target)
      (SetFunction. (first-set source) (first-set target) morphism-function)
      (SetFunction. (second-set source) (second-set target) object-function)))

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (->Diamond
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      (SetFunction.
        (inputs (source-object this))
        (inputs (target-object this))
        (fn [[morphism1 morphism2]]
          (list
            (morphism-function morphism1)
            (morphism-function morphism2))))
      (SetFunction.
        (outputs (source-object this))
        (outputs (target-object this))
        morphism-function))))

(derive GroupoidFunctor :locus.elementary.function.core.protocols/groupoid-functor)

; Composition and identities in the category of groupoids
(defmethod compose* GroupoidFunctor
  [^GroupoidFunctor f, ^GroupoidFunctor g]

  (GroupoidFunctor.
    (source-object g)
    (target-object f)
    (comp (.morphism-function f) (.morphism-function g))
    (comp (.object-function f) (.object-function g))))

(defmethod identity-morphism Groupoid
  [groupoid]

  (GroupoidFunctor. groupoid groupoid identity identity))