(ns locus.elementary.semigroup.monoid.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all])
  (:import [locus.elementary.function.core.object SetFunction]
           [locus.elementary.diamond.core.object Diamond]
           (locus.elementary.semigroup.monoid.object Monoid)))

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
  (first-function [this]
    (SetFunction. (inputs this) (outputs this) func))
  (second-function [this]
    (SetFunction. #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Monoid homomorphisms are also morphisms of functions
  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (let [sf (SetFunction.
               (inputs in-monoid)
               (outputs out-monoid)
               func)]
      (Diamond.
        (underlying-function in-monoid)
        (underlying-function out-monoid)
        (function-product sf sf)
        sf))))

(derive MonoidMorphism :locus.elementary.function.core.protocols/monoid-homomorphism)

(defn monoid-homomorphism?
  [func]

  (or
    (= (type func) MonoidMorphism)
    (and
      (functor? func)
      (monoid? (source-object func))
      (monoid? (target-object func)))))

; Identity element function morphisms
(defn morphism-of-identity-element-functions
  [func]

  (Diamond.
    (identity-element-function (source-object func))
    (identity-element-function (target-object func))
    (identity-function #{'()})
    (underlying-function func)))

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