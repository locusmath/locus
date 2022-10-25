(ns locus.nonassociative.action.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.permutation :refer :all]
            [locus.base.effects.global.transformation :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.partial.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.category.partial.bijection :refer :all]
            [locus.elementary.category.partial.transformation :refer :all]
            [locus.elementary.category.partial.permutation :refer :all]
            [locus.nonassociative.magma.object :refer :all]
            [locus.nonassociative.magmoid.object :refer :all]
            [locus.nonassociative.partial-magma.object :refer :all]
            [locus.nonassociative.partial-magma.object :refer :all]
            [locus.nonassociative.partial-magma.morphism :refer :all])
  (:import (locus.elementary.action.global.object MSet)
           (locus.elementary.semigroup.partial.object PartialTransformationSemigroup)))

; Let C be a category. Then C is associated to two different sets: its object set and its morphism
; set. We say that the morphism set has the structure of a partial semigroup (Arrows(C),*) in
; which the product of two morphisms is only defined when they have a common intermediate object
; between them. On the other hand, by this same principle the objects set Ob(C) has the structure
; of a partial semigroup action by partial transformations, where each partial transformation
; is an atomic chart on objects. The action of a morphism f: A to B is the partial transformation
; (A,B) on Ob(C) which is defined only on A and which moves it to C.

; The actions of categories and their generalisations such as partial magmoids are always actions
; by atomic charts, which are defined by only one element but by generality we can also define
; the most general concept of a partial algebraic action to be the action of some partial magma
; by any partial transformations. By this approach we arrive at the concept of a PSet, which is
; so named by generalisation of the idea of an MSet in total algebra. A PSet is the partial
; algebraic generalisation of the concept of an MSet. A PSet is equivalent to a partial magma
; homomorphism from some partial magma into the full partial transformation semigroup on a set.

; Partial action system
; The partial algebraic generalisation of the concept of an MSet.
(deftype PSet [magma coll action]
  ConcreteObject
  (underlying-set [this] coll)

  EffectSystem
  (actions [this]
    (morphisms magma))
  (action-domain [this elem]
    (relation-domain (underlying-relation (action elem))))
  (apply-action [this elem arg]
    ((action elem) arg)))

(derive PSet :locus.base.logic.structure.protocols/structured-set)

; Generalized conversion routines for actions on sets in partial algebra
(defmulti to-pset type)

(defmethod to-pset PSet
  [obj] obj)

(defmethod to-pset MSet
  [^MSet action]

  (let [coll (.-coll action)]
    (->PSet
      (.-monoid action)
      coll
      (fn [a]
        (->PartialTransformation
          coll
          coll
          (fn [x]
            (apply-action action a x)))))))

(defmethod to-pset PartialTransformationSemigroup
  [^PartialTransformationSemigroup semigroup]

  (->PSet
    (.-semigroup semigroup)
    (.-coll semigroup)
    (.-func semigroup)))

; We can treat the object set of a category as like a sort of action in partial algebra
(defn morphic-action-on-objects
  [magmoid]

  (PSet.
    (composition-operation magmoid)
    (objects magmoid)
    (fn [morphism]
      (->AtomicChart
        (objects magmoid)
        (source-element magmoid morphism)
        (target-element magmoid morphism)))))

(defmethod to-pset :locus.elementary.copresheaf.core.protocols/partial-magmoid
  [magmoid] (morphic-action-on-objects magmoid))

; Get a partial transformation action
(defn action-partial-transformation
  [ps action]

  ((.action ps) action))

; Partial action preorders
(defmethod action-preorder PSet
  [ps]

  (cl preorder?
      (apply
        union
        (map
          (fn [i]
            (underlying-relation (action-partial-transformation ps i)))
          (actions ps)))))

; Create a full semigroup of partial transformation PT_{S}
(defn full-partial-transformation-semigroup
  [coll]

  (->Semigroup
    (fn [elem]
      (and
        (partial-transformation? elem)
        (equal-universals? (source-object elem) coll)))
    (fn [[a b]]
      (compose a b))))

(defmethod action-homomorphism PSet
  [^PSet ps]

  (->PartialMagmaMorphism
    (.-magma ps)
    (full-partial-transformation-semigroup (.-coll ps))
    (.-action ps)))

(defmethod to-partial-magma-homomorphism PSet
  [^PSet ps] (action-homomorphism ps))

; Create a partial semigroup action by atomic charts
(defn atomic-charts-pset
  [rel]

  (let [coll (vertices rel)]
    (->PSet
      (transition-partial-magma rel)
      coll
      (fn [[a b]]
        (->AtomicChart
          coll
          a
          b)))))

; We need to be able to find some way of getting partial transformations from
; the morphic elements of a category based upon how they operate on one another
(defn left-self-partial-transformation
  [category action]

  (->PartialTransformation
    (seqable-filter
      (fn [arg]
        (composable-elements? category action arg))
      (morphisms category))
    (morphisms category)
    (fn [arg]
      (category (list action arg)))))

(defn right-self-partial-transformation
  [category action]

  (->PartialTransformation
    (seqable-filter
      (fn [arg]
        (composable-elements? category arg action))
      (morphisms category))
    (morphisms category)
    (fn [arg]
      (category (list arg action)))))

(defn two-sided-self-partial-transformation
  [category left-action right-action]

  (->PartialTransformation
    (let [source (target-element category right-action)
          target (source-element category left-action)]
      (quiver-hom-class category source target))
    (morphisms category)
    (fn [arg]
      (category (list left-action (category (list arg right-action)))))))

; We can now create partial action systems that correspond to the various
; different kinds of partial transformations that we have encountered already
(defn left-self-partial-action
  [category]

  (PSet.
    (morphisms category)
    (morphisms category)
    (fn [left-action]
      (left-self-partial-transformation category left-action))))

(defn right-self-partial-action
  [category]

  (PSet.
    (morphisms category)
    (morphisms category)
    (fn [right-action]
      (right-self-partial-transformation category right-action))))

(defn two-sided-self-partial-action
  [category]

  (PSet.
    (product (morphisms category) (morphisms category))
    (morphisms category)
    (fn [[left-action right-action]]
      (two-sided-self-partial-transformation category left-action right-action))))

; Ontology of partial action systems
(defmulti pset? type)

(defmethod pset? PSet
  [obj] true)

(defn atomic-chart-pset?
  [ps]

  (and
    (pset? ps)
    (every?
      (fn [i]
        (let [action (action-partial-transformation ps i)]
          (atomic-chart? action)))
      (morphisms ps))))

(defn partial-permutation-pset?
  [ps]

  (and
    (pset? ps)
    (every?
      (fn [i]
        (let [action (action-partial-transformation ps i)]
          (partial-permutation? action)))
      (morphisms ps))))

(defn transitive-pset?
  [ps]

  (and
    (pset? ps)
    (complete-relation? (action-preorder ps))))

(defn transitive-atomic-charts-pset?
  [ps]

  (and
    (atomic-chart-pset? ps)
    (complete-relation? (action-preorder ps))))

(defn transitive-partial-permutation-pset?
  [ps]

  (and
    (partial-permutation-pset? ps)
    (complete-relation? (action-preorder ps))))