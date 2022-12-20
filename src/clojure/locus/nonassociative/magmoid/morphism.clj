(ns locus.nonassociative.magmoid.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.nonassociative.magma.object :refer :all]
            [locus.nonassociative.magma.morphism :refer :all]
            [locus.nonassociative.magmoid.object :refer :all])
  (:import (locus.nonassociative.magma.object Magma)
           (locus.nonassociative.magmoid.object Magmoid)
           (locus.nonassociative.magma.morphism MagmaMorphism)))

; A magmoid functor is a homomorphism in the category of magmoids. Magmoids in turn are
; defined as the horizontal categorification of the concept of a magma, so they are
; nonassociative generalisations of categories or magmas with multiple objects.
; As is the case for categories, homomorphisms of magmoids can be defined by morphism
; of their underlying quivers subject to some extra conditions. So the functor from the
; category of magmoids to the category of quivers is faithful.

(deftype MagmoidFunctor [source target object-function morphism-function]
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

(derive MagmoidFunctor :locus.set.copresheaf.structure.core.protocols/magmoid-homomorphism)

(defmulti to-magmoid-functor type)

(defmethod to-magmoid-functor MagmoidFunctor
  [morphism] morphism)

(defmethod to-magmoid-functor MagmaMorphism
  [func]

  (->MagmoidFunctor
    (to-magmoid (source-object func))
    (to-magmoid (target-object func))
    func
    identity))

(defmethod compose* MagmoidFunctor
  [a b]

  (->MagmoidFunctor
    (source-object b)
    (target-object a)
    (comp (first-function a) (first-function b))
    (comp (second-function a) (second-function b))))

(defmethod identity-morphism Magmoid
  [magmoid]

  (->MagmoidFunctor
    magmoid
    magmoid
    identity
    identity))
