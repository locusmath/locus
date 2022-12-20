(ns locus.algebra.semigroup.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.mapping.general.core.object SetFunction]
           [locus.set.quiver.unary.core.morphism Diamond]
           (locus.algebra.semigroup.core.object Semigroup)))

; A semigroup morphism is a structured function, because the category of semigroups
; is a concrete category. We also introduce a map to morphisms of functions over
; every semigroup by the functor to the topos Sets^(->).

(deftype SemigroupMorphism [in-semigroup out-semigroup func]
  ; Semigroup homomorphisms are functions of semigroups
  AbstractMorphism
  (source-object [this] in-semigroup)
  (target-object [this] out-semigroup)

  ConcreteMorphism
  (inputs [this] (underlying-set in-semigroup))
  (outputs [this] (underlying-set out-semigroup))

  StructuredDifunction
  (first-function [this] (SetFunction. (inputs this) (outputs this) func))
  (second-function [this] (SetFunction. #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ; Semigroup homomorphisms are also morphisms of functions
  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-binary-operations
      (underlying-function in-semigroup)
      (underlying-function out-semigroup)
      (SetFunction. (inputs this) (outputs this) func))))

(derive SemigroupMorphism :locus.set.copresheaf.structure.core.protocols/semigroup-homomorphism)

(defn semigroup-homomorphism?
  [func]

  (and
    (semifunctor? func)
    (and
      (semigroup? (source-object func))
      (semigroup? (target-object func)))))

; Test for functoriality
(defmethod functor? SemigroupMorphism
  [func]

  (and
    (monoid? (source-object func))
    (monoid? (target-object func))
    (let [source-identity (first (identity-elements (source-object func)))
          target-identity (first (identity-elements (target-object func)))]
      (= (func source-identity) target-identity))))

; Image and congruence quotients of semigroup homomorphisms
(defn image-semigroup
  [func]

  (restrict-semigroup (target-object func) (function-image func)))

(defn kernel-quotient-semigroup
  [func]

  (quotient-semigroup (source-object func) (function-kernel func)))

; Join and meet components of lattice homomorphisms
(defn morphism-of-join-semilattices
  [lattice-homomorphism]

  (->SemigroupMorphism
    (join-semilattice (source-object lattice-homomorphism))
    (join-semilattice (target-object lattice-homomorphism))
    (underlying-function lattice-homomorphism)))

(defn morphism-of-meet-semilattices
  [lattice-homomorphism]

  (->SemigroupMorphism
    (meet-semilattice (source-object lattice-homomorphism))
    (meet-semilattice (target-object lattice-homomorphism))
    (underlying-function lattice-homomorphism)))

; Morphisms of the component functions of a lattice
(defn morphism-of-join-functions
  [morphism]

  (morphism-of-binary-operations
    (join-function (source-object morphism))
    (join-function (target-object morphism))
    (underlying-function morphism)))

(defn morphism-of-meet-functions
  [morphism]

  (morphism-of-binary-operations
    (meet-function (source-object morphism))
    (meet-function (target-object morphism))
    (underlying-function morphism)))

; Composition and identities in the category of semigroups
(defmethod compose* SemigroupMorphism
  [a b]

  (SemigroupMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (SemigroupMorphism. semigroup semigroup identity))

