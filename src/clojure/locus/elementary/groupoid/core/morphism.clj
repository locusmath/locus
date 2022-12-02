(ns locus.elementary.groupoid.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.groupoid.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.base.function.core.object SetFunction)
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
  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-partial-binary-operations
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      morphism-function)))

(derive GroupoidFunctor :locus.elementary.copresheaf.core.protocols/groupoid-functor)

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