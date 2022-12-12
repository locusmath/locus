(ns locus.additive.semiring.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.algebra.semigroup.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.arithmetic :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.group.core.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all])
  (:import (locus.additive.semiring.core.object Semiring)))

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
(defmethod identity-morphism :locus.additive.base.core.protocols/semiring
  [semiring]

  (SemiringMorphism. semiring semiring identity))

(defmethod compose* SemiringMorphism
  [a b]

  (SemiringMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; Ontology of semiring homomorphisms
(defn semiring-morphism?
  [morphism]

  (= (type morphism) SemiringMorphism))