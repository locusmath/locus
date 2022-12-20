(ns locus.algebra.groupoid.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.morphism :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.groupoid.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (locus.algebra.groupoid.core.object Groupoid)))

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

(derive GroupoidFunctor :locus.set.copresheaf.structure.core.protocols/groupoid-functor)

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