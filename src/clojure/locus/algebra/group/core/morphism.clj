(ns locus.algebra.group.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (locus.set.quiver.unary.core.morphism Diamond)
           (locus.algebra.group.core.object Group)))

; As groups are monoids with additional structure, the category of groups is equipped
; with an additional functor to Sets^(->) by its inversion function. So we provide
; a special class of group homomorphisms for dealing with extra functionality
; entailed by the category of groups.

(deftype GroupMorphism [in-group out-group func]
  AbstractMorphism
  (source-object [this] in-group)
  (target-object [this] out-group)

  ConcreteMorphism
  (inputs [this] (underlying-set in-group))
  (outputs [this] (underlying-set out-group))

  StructuredDifunction
  (first-function [this] (SetFunction. (inputs this) (outputs this) func))
  (second-function [this] (SetFunction. #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-binary-operations
      (underlying-function in-group)
      (underlying-function out-group)
      (SetFunction. (inputs this) (outputs this) func))))

(derive GroupMorphism :locus.set.copresheaf.structure.core.protocols/group-homomorphism)

; Constructors for group homomorphisms
(defn group-homomorphism
  [source target func]

  (->GroupMorphism
    source
    target
    func))

(defn group-endomorphism
  [group func]

  (->GroupMorphism
    group
    group
    func))

; Get the morphism of functions of the inverse functions of two
; groups induced by a group homomorphism
(defn morphism-of-inverse-functions
  [morphism]

  (Diamond.
    (inverse-function (source-object morphism))
    (inverse-function (target-object morphism))
    (underlying-function morphism)
    (underlying-function morphism)))

; Composition and identities in the category of groups
(defmethod compose* GroupMorphism
  [a b]

  (GroupMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism Group
  [group]

  (GroupMorphism. group group identity))

; Kernel of group homomorphism
(defn kernel-subgroup
  [morphism]

  (restrict-group
    (source-object morphism)
    (set
      (let [target-identity (.id (target-object morphism))]
        (filter
          (fn [i]
            (= (morphism i) target-identity))
          (underlying-set (target-object morphism)))))))

(defn image-subgroup
  [morphism]

  (restrict-group
    (target-object morphism)
    (function-image morphism)))

; Ontology
(defn group-homomorphism?
  [func]

  (or
    (= (type func) GroupMorphism)
    (and
      (functor? func)
      (group? (source-object func))
      (group? (target-object func)))))

