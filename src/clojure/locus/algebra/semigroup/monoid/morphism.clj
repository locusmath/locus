(ns locus.algebra.semigroup.monoid.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all])
  (:import [locus.set.mapping.general.core.object SetFunction]
           [locus.set.quiver.unary.core.morphism Diamond]
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

(derive MonoidMorphism :locus.set.copresheaf.structure.core.protocols/monoid-homomorphism)

; Constructors for monoid homomorphisms
(defn monoid-homomorphism
  [source target func]

  (->MonoidMorphism
    source
    target
    func))

(defn monoid-endomorphism
  [monoid func]

  (->MonoidMorphism
    monoid
    monoid
    func))

; Ontology of monoid homomorphisms
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