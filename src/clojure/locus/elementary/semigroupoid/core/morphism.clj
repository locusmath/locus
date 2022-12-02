(ns locus.elementary.semigroupoid.core.morphism
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
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.semigroupoid.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.semigroupoid.core.object Semigroupoid)))

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
(derive Semifunctor :locus.elementary.copresheaf.core.protocols/semifunctor)

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

