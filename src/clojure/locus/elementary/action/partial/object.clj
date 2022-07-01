(ns locus.elementary.action.partial.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.action.effects.permutation :refer :all]
            [locus.elementary.action.effects.transformation :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.relational.function.partial-set-function :refer :all]
            [locus.elementary.relational.function.partial-transformation :refer :all]))

; Let C be a category, and Arrows(C) its morphism set. Then the morphisms of C act on Arrows(C)
; by self induced actions. This produces a structure which we call a partial action system,
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






