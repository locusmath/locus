(ns locus.elementary.category.semigroupoid.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.semigroupoid.object :refer :all])
  (:import (locus.elementary.category.semigroupoid.object Semigroupoid)
           (locus.elementary.function.core.object SetFunction)))

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

; The position of semifunctors in the type hierarchy
(derive Semifunctor :locus.elementary.function.core.protocols/semifunctor)

; Composition functions
(defmethod compose* Semifunctor
  [^Semifunctor f ^Semifunctor g]

  (Semifunctor.
    (source-object g)
    (target-object f)
    (comp (.morphism-function f) (.morphism-function g))
    (comp (.object-function f) (.object-function g))))

(defmethod identity-morphism Semigroupoid
  [category]

  (Semifunctor. category category identity identity))



