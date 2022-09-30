(ns locus.elementary.group.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.group.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.diamond.core.object Diamond)
           (locus.elementary.group.core.object Group)))

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
  (first-function [this]
    (SetFunction. (inputs this) (outputs this) func))
  (second-function [this]
    (SetFunction. #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (let [sf (SetFunction.
               (inputs in-group)
               (outputs out-group)
               func)]
      (Diamond.
        (underlying-function in-group)
        (underlying-function out-group)
        (function-product sf sf)
        sf))))

(derive GroupMorphism :locus.elementary.copresheaf.core.protocols/group-homomorphism)

; Ontology
(defn group-homomorphism?
  [func]

  (or
    (= (type func) GroupMorphism)
    (and
      (functor? func)
      (group? (source-object func))
      (group? (target-object func)))))

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

