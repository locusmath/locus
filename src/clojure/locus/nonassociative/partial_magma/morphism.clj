(ns locus.nonassociative.partial-magma.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.two-quiver.core.object :refer :all]
            [locus.elementary.two-quiver.path.object :refer :all]
            [locus.nonassociative.partial-magma.object :refer :all])
  (:import (locus.nonassociative.partial_magma.object PartialMagma)))

; A morphism in the category of partial magmas is a function f: M -> N between the underlying
; sets of two partial magmas such that with respect to the existence domain R of M we have
; that for all (a,b) in R it is the case that ab = f(a)f(b). So it is an ordinary algebraic
; homomorphism but only defined over a partially existing domain. Every such homomorphism
; of partial magmas induces a homomorphism in the category of binary relations from the
; partial existence domains of partial magmas. This relationship is functorial, and defines
; a functor from the category of partial magmas to the category of binary relations.

(deftype PartialMagmaMorphism [source target func]
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
    (morphism-of-partial-binary-operations
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      func)))

(derive PartialMagmaMorphism :locus.elementary.copresheaf.core.protocols/partial-magma-homomorphism)

(defmulti to-partial-magma-homomorphism type)

(defmethod to-partial-magma-homomorphism PartialMagmaMorphism
  [morphism] morphism)

(defn morphism-of-domain-quivers
  [morphism]

  (->MorphismOfQuivers
    (domain-quiver (source-object morphism))
    (domain-quiver (target-object morphism))
    (->SetFunction
      (inputs (source-object morphism))
      (inputs (target-object morphism))
      (fn [[a b]]
        (list (morphism a) (morphism b))))
    (underlying-function morphism)))

(defn partial-magma-homomorphism?
  [func]

  (and
    (partial-magmoid-homomorphism? func)
    (and
      (partial-magma? (source-object func))
      (partial-magma? (target-object func)))))

(defmethod compose* PartialMagmaMorphism
  [a b]

  (->PartialMagmaMorphism
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

(defmethod identity-morphism PartialMagma
  [magma]

  (->PartialMagmaMorphism magma magma identity))
