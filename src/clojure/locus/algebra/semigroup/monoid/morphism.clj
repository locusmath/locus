(ns locus.algebra.semigroup.monoid.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.diset.core.morphism :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           [locus.quiver.unary.core.morphism Diamond]
           (locus.algebra.semigroup.monoid.object Monoid)))

; The category of monoids is a full subcategory of the category of categories.
; It naturally follows that monoid morphisms are functors, and so we provide
; special support for these functors here. These are distinguished from other
; functors by the fact that Mon is represented as a concrete category with a
; forgetful functor to its set of objects.

(deftype MonoidMorphism [in-monoid out-monoid func]
  ; Monoids homomorphisms are functions of monoids
  AbstractMorphism
  (source-object [this] in-monoid)
  (target-object [this] out-monoid)

  ConcreteMorphism
  (inputs [this] (underlying-set in-monoid))
  (outputs [this] (underlying-set out-monoid))

  StructuredDifunction
  (first-function [this] (SetFunction. (inputs this) (outputs this) func))
  (second-function [this] (SetFunction. #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Monoid homomorphisms are also morphisms of functions
  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-binary-operations
      (underlying-function in-monoid)
      (underlying-function out-monoid)
      (SetFunction. (inputs this) (outputs this) func))))

(derive MonoidMorphism :locus.elementary.copresheaf.core.protocols/monoid-homomorphism)

(defn monoid-homomorphism?
  [func]

  (or
    (= (type func) MonoidMorphism)
    (and
      (functor? func)
      (monoid? (source-object func))
      (monoid? (target-object func)))))

; Composition and identities
(defmethod compose* MonoidMorphism
  [a b]

  (MonoidMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism Monoid
  [semigroup]

  (MonoidMorphism. semigroup semigroup identity))