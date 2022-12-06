(ns locus.partial-algebra.partial-magmoid.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.partial-algebra.partial-magma.object :refer :all]
            [locus.partial-algebra.partial-magma.morphism :refer :all]
            [locus.partial-algebra.partial-magmoid.object :refer :all])
  (:import (locus.partial_algebra.partial_magmoid.object PartialMagmoid)
           (locus.partial_algebra.partial_magma.morphism PartialMagmaMorphism)))

; A partial magmoid functor is a homomorphism of partial magmoids. It is the horizontal
; categorification of the concept of a homomorphism of partial magmas. A partial magmoid
; homomorphism is defined by an existence homomorphism of the underlying partial path
; relations of the two partial magmoids as well as an algebraic homomorphism of the two
; compositional magma structures of the two partial magmoids.

(deftype PartialMagmoidFunctor [source target object-function morphism-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function)

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-partial-binary-operations
      (underlying-function source)
      (underlying-function target)
      morphism-function)))

(derive PartialMagmoidFunctor :locus.elementary.copresheaf.core.protocols/partial-magmoid-homomorphism)

; Conversion to partial magmoid functors
(defmulti to-partial-magmoid-functor type)

(defmethod to-partial-magmoid-functor PartialMagmoidFunctor
  [obj] obj)

(defmethod to-partial-magmoid-functor PartialMagmaMorphism
  [func]

  (->PartialMagmoidFunctor
    (to-partial-magmoid (source-object func))
    (to-partial-magmoid (target-object func))
    func
    identity))

; Composition and identities in the category of partial magmoids
(defmethod compose* PartialMagmoidFunctor
  [a b]

  (->PartialMagmoidFunctor
    (source-object b)
    (target-object a)
    (comp (first-function a) (first-function b))
    (comp (second-function a) (second-function b))))

(defmethod identity-morphism PartialMagmoid
  [magmoid]

  (->PartialMagmoidFunctor
    magmoid
    magmoid
    identity
    identity))

(defn morphism-of-composition-partial-magmas
  [functor]

  (->PartialMagmaMorphism
    (composition-operation (source-object functor))
    (composition-operation (target-object functor))
    (morphism-component-function functor)))