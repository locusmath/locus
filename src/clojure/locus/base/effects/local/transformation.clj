(ns locus.base.effects.local.transformation
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.lens.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.effects.global.transformation :refer :all]))

; Local transformations
; A local transformation is an endofunction localized to some lens. As a consequence, it has two
; partition equal congruences: the getter congruence and the setter congruence produced by
; the lens it is localized to.
(deftype LocalTransformation
  [lens out func]

  ConcreteMorphism
  (inputs [this] (underlying-set lens))
  (outputs [this] (underlying-set lens))

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this arg]
    (zap lens arg func))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive LocalTransformation :locus.base.logic.structure.protocols/transformation)

(defn local-transformation-quotient
  [^LocalTransformation func]

  (->Transformation
    (.-out func)
    (.-func func)))

(defmethod globalize LocalTransformation
  [func]

  (->Transformation
    (inputs func)
    (fn [x]
      (func x))))