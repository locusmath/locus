(ns locus.elementary.action.effects.local-transformation
  (:require [locus.elementary.logic.base.core :refer :all]

            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]

            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.action.effects.permutation :refer :all]
            [locus.elementary.action.effects.transformation :refer :all]
            [locus.elementary.lens.core.object :refer :all]))

; Local transformations are distinguished from global ones by the fact that
; their action occurs on a functional lens.
(deftype LocalTransformation
  [lens func]

  ConcreteObject
  (underlying-set [this]
    (inputs lens))

  ConcreteMorphism
  (inputs [this] (inputs lens))
  (outputs [this] (inputs lens))

  clojure.lang.IFn
  (invoke [this arg]
    (zap lens arg func))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defn local-transformation-quotient
  [func]

  (->Transformation (outputs (.lens func)) (.func func)))

(defmethod globalize LocalTransformation
  [func]

  (->Transformation
    (underlying-set func)
    (fn [x]
      (func x))))

(defmethod visualize LocalTransformation
  [func] (visualize (globalize func)))