(ns locus.elementary.action.local.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lens.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.action.effects.permutation :refer :all]
            [locus.elementary.action.effects.transformation :refer :all]
            [locus.elementary.action.effects.local-permutation :refer :all]
            [locus.elementary.action.effects.local-transformation :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.action.core.protocols :refer :all])
  (:import (locus.elementary.action.effects.local_permutation LocalPermutation)
           (locus.elementary.action.effects.local_transformation LocalTransformation)))

; A lens type can be defined by a pair of congruences in a topos of monoid actions.
; On the other hand, a lens itself is defined by a pair consisting of a getter
; and a setter. If we take a lens then we can produce local monoid actions that
; handle only the memory location defined by the lens. This is a part of our
; developing topos theoretic model of computation.

; The only question is how to apply actions
(deftype LocalMSet [lens mset]
  ConcreteObject
  (underlying-set [this]
    (inputs lens))

  EffectSystem
  (actions [this] (actions mset))
  (action-domain [this action] (inputs lens))
  (apply-action [this action x]
    (zap
      lens
      x
      (fn [prop]
        (apply-action mset action prop)))))

(derive LocalMSet :locus.elementary.function.core.protocols/mset)

; Special methods for local monoid actions
(defmethod globalize LocalMSet
  [ms]

  (->MSet
    (.monoid (.mset ms))
    (underlying-set ms)
    (fn [a x] (apply-action ms a x))))

(defmethod to-mset LocalMSet
  [action] action)

(defmethod to-mset LocalPermutation
  [func]

  (new LocalMSet (.lens func) (to-mset (local-permutation-quotient func))))

(defmethod to-mset LocalTransformation
  [func]

  (new LocalMSet (.lens func) (to-mset (local-transformation-quotient func))))

