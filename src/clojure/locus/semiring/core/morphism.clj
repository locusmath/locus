(ns locus.semiring.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.semiring.core.object :refer :all]
            [locus.ring.core.protocols :refer :all])
  (:import (locus.semiring.core.object Semiring)))

; Morphisms in the category of semirings
; This class provides support for morphisms in the category of semirings. The
; category of semirings is characterized by a number of forgetful functors
; to various other categories, such as the category of semigroups. In particular,
; semiring morphisms induce morphisms of additive and multiplicative semigroups.

(deftype SemiringMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Morphism of additive components
(defn morphism-of-additive-semigroups
  [^SemiringMorphism morphism]

  (->SemigroupMorphism
    (additive-semigroup (source-object morphism))
    (additive-semigroup (target-object morphism))
    (.func morphism)))

(defn morphism-of-multiplicative-semigroups
  [^SemiringMorphism morphism]

  (->SemigroupMorphism
    (multiplicative-semigroup morphism)
    (multiplicative-semigroup morphism)
    (.func morphism)))

; Morphism parts of functors to the topos of functions
(def morphism-of-addition-functions
  (comp underlying-morphism-of-functions morphism-of-additive-semigroups))

(def morphism-of-additive-identity-functions
  (comp morphism-of-identity-element-functions morphism-of-additive-semigroups))

(def morphism-of-additive-inverse-functions
  (comp morphism-of-inverse-functions morphism-of-additive-semigroups))

(def morphism-of-multiplicative-semigroups
  (comp underlying-morphism-of-functions morphism-of-multiplicative-semigroups))

(def morphism-of-multiplicative-identity-functions
  (comp morphism-of-identity-element-functions morphism-of-multiplicative-semigroups))

; Identity morphisms
(defmethod identity-morphism Semiring
  [semiring]

  (SemiringMorphism. semiring semiring identity))

(defmethod compose* SemiringMorphism
  [a b]

  (SemiringMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))