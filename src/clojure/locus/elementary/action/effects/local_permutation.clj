(ns locus.elementary.action.effects.local-permutation
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.action.effects.transformation :refer :all]
            [locus.elementary.action.effects.permutation :refer :all]
            [locus.elementary.lens.core.object :refer :all]))

; Local permutations are distinguished from global ones by the fact that
; their transformation occurs on a functional lens.
(deftype LocalPermutation [lens perm]
  ConcreteObject
 (underlying-set [this]
   (inputs lens))

  ConcreteMorphism
  (inputs [this] (inputs lens))
  (outputs [this] (inputs lens))

  clojure.lang.IFn
  (invoke [this obj]
    (zap lens obj perm))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args))

  StructuredBijection
  (underlying-bijection [this]
    (->Bijection
      (inputs lens)
      (inputs lens)
      (fn [x]
        (zap lens x perm))
      (fn [x]
        (zap lens x (inv perm)))))

  Invertible
  (inv [this]
    (LocalPermutation. lens (inv perm))))

(defn local-permutation-quotient
  [func]

  (let [local-permutation (.perm func)]
    (->Permutation
      (outputs (.lens func))
      local-permutation
      (inv local-permutation))))

(defmethod globalize LocalPermutation
  [func]

  (->Permutation
    (underlying-set func)
    (fn [x] (func x))
    (fn [x] ((inv func) x))))

(defmethod visualize LocalPermutation
  [func] (visualize (globalize func)))