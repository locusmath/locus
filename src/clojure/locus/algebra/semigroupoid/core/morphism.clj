(ns locus.algebra.semigroupoid.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.semigroupoid.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (locus.algebra.semigroupoid.core.object Semigroupoid)))

; A functor is a morphism of categories that preserves composition, the
; underlying quiver relations, and identities. So by generalisation a semifunctor
; is simply a morphism that preserves everything but the identities. Together with
; semigroupoids, the semifunctors define the category of semigroupoids.
(deftype Semifunctor [source target morphism-function object-function]
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

; The position of semifunctors in the type hierarchy
(derive Semifunctor :locus.set.copresheaf.structure.core.protocols/semifunctor)

; Composition functions
(defmethod compose* Semifunctor
  [^Semifunctor f, ^Semifunctor g]

  (Semifunctor.
    (source-object g)
    (target-object f)
    (comp (first-function f) (first-function g))
    (comp (first-function f) (first-function g))))

(defmethod identity-morphism Semigroupoid
  [category]

  (Semifunctor. category category identity identity))

; Endomorphisms in the category of semigroupoids
(defn endosemifunctor?
  [func]

  (and
    (semifunctor? func)
    (= (source-object func) (target-object func))))

