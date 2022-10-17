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
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.category.partial.function :refer :all]
            [locus.elementary.category.partial.bijection :refer :all]
            [locus.elementary.category.partial.transformation :refer :all]
            [locus.elementary.category.partial.permutation :refer :all]))

; Let C be a category, and Arrows(C) its morphism set. Then the morphisms of C act on Arrows(C)
; by self-induced actions. This produces a structure which we call a partial action system,
; which has a lot in common with monoid actions. These partial action systems can also
; be produced by semigroups of partial permutations and transformations.

; Partial action system
; This actually maps a given action directly to a function
(deftype PartialActionSystem [actions coll func]
  ConcreteObject
  (underlying-set [this] coll)

  EffectSystem
  (actions [this] actions)
  (apply-action [this action arg] ((func action) arg))
  (action-domain [this action]
    (relation-domain (underlying-relation (func action)))))

(derive PartialActionSystem :locus.base.logic.structure.protocols/structured-set)

; Conversion of structures to partial action systems
(defmulti to-partial-action-system type)

(defmethod to-partial-action-system PartialActionSystem
  [structure] PartialActionSystem)

; Get a partial transformation action
(defn action-partial-transformation
  [ps action]

  ((.func ps) action))

; Partial action preorders
(defmethod action-preorder PartialActionSystem
  [ps]

  (cl preorder?
      (apply
        union
        (map
          (fn [i]
            (underlying-relation (action-partial-transformation ps i)))
          (.actions ps)))))

; Object action
(defn object-action
  [category]

  (PartialActionSystem.
    (morphisms category)
    (objects category)
    (fn [morphism]
      (->AtomicChart
        (objects category)
        (source-element category morphism)
        (target-element category morphism)))))

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

  (PartialActionSystem.
    (morphisms category)
    (morphisms category)
    (fn [left-action]
      (left-self-partial-transformation category left-action))))

(defn right-self-partial-action
  [category]

  (PartialActionSystem.
    (morphisms category)
    (morphisms category)
    (fn [right-action]
      (right-self-partial-transformation category right-action))))

(defn two-sided-self-partial-action
  [category]

  (PartialActionSystem.
    (product (morphisms category) (morphisms category))
    (morphisms category)
    (fn [[left-action right-action]]
      (two-sided-self-partial-transformation category left-action right-action))))






