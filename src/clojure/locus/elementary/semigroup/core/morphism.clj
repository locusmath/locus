(ns locus.elementary.semigroup.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.core.morphism :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           [locus.elementary.diamond.core.object Diamond]
           (locus.elementary.semigroup.core.object Semigroup)))

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

(derive SemigroupMorphism :locus.elementary.copresheaf.core.protocols/semigroup-homomorphism)

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

; Composition and identities in the category of semigroups
(defmethod compose* SemigroupMorphism
  [a b]

  (SemigroupMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism Semigroup
  [semigroup]

  (SemigroupMorphism. semigroup semigroup identity))

