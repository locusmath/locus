(ns locus.base.effects.local.permutation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.lens.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.transformation :refer :all]
            [locus.base.effects.global.permutation :refer :all]
            [locus.base.effects.local.transformation :refer :all]))

; Local permutation
; A local permutation is an automorphism of Sets localized to some lens. It is also a special
; type of invertible function, as described by the fact that it is a permutation.
(deftype LocalPermutation
  [lens out forward backward]

  ConcreteMorphism
  (inputs [this] (underlying-set lens))
  (outputs [this] (underlying-set lens))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  Invertible
  (inv [this]
    (LocalPermutation. lens out backward forward))

  clojure.lang.IFn
  (invoke [this arg]
    (zap lens arg forward))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive LocalPermutation :locus.base.logic.structure.protocols/permutation)

(defn local-permutation-quotient
  [^LocalPermutation func]

  (->Permutation
    (.-out func)
    (.-forward func)
    (.-backward func)))

(defmethod globalize LocalPermutation
  [^LocalPermutation func]

  (->Permutation
    (inputs func)
    (.forward func)
    (.backward func)))