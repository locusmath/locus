(ns locus.set.mapping.effects.local.permutation
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.logic.lens.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.effects.global.transformation :refer :all]
            [locus.set.mapping.effects.global.permutation :refer :all]
            [locus.set.mapping.effects.local.transformation :refer :all]))

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

(derive LocalPermutation :locus.set.logic.structure.protocols/permutation)

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