(ns locus.nonassociative.magma.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.nonassociative.magma.object :refer :all])
  (:import (locus.set.quiver.unary.core.morphism Diamond)
           (locus.set.mapping.general.core.object SetFunction)
           (locus.nonassociative.magma.object Magma)))

; A magma homomorphism is a structured function, because it defines a mapping from one
; structured set to another. This means it is like a presheaf of magmas over the
; ordered pair category. In another sense, magmas are like magmoids and this makes them
; like generalized functors over non-associative categories. Finally, given a presheaf
; representation of the compositional quiver type, it is like a morphism of presheaves.

(deftype MagmaMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  StructuredDifunction
  (first-function [this] (->SetFunction (inputs this) (outputs this) func))
  (second-function [this] (->SetFunction #{0} #{0} {0 0}))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args))

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-binary-operations
      (underlying-function source)
      (underlying-function target)
      (SetFunction. (inputs this) (outputs this) func))))

(derive MagmaMorphism :locus.set.copresheaf.structure.core.protocols/magma-homomorphism)

(defmulti to-magma-homomorphism type)

(defmethod to-magma-homomorphism MagmaMorphism
  [morphism] morphism)

(defn magma-homomorphism?
  [func]

  (and
    (magmoid-homomorphism? func)
    (and
      (magma? (source-object func))
      (magma? (target-object func)))))

(defmethod compose* MagmaMorphism
  [a b]

  (->MagmaMorphism
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism Magma
  [magma]

  (->MagmaMorphism magma magma identity))