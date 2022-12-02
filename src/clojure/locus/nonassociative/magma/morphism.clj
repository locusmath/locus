(ns locus.nonassociative.magma.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.nonassociative.magma.object :refer :all])
  (:import (locus.quiver.unary.core.morphism Diamond)
           (locus.base.function.core.object SetFunction)
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

(derive MagmaMorphism :locus.elementary.copresheaf.core.protocols/magma-homomorphism)

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