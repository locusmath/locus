(ns locus.base.function.operations.mf
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.limit.power :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]))

; A data type for describing magma functions
(deftype MagmaFunction [coll func]
  ConcreteMorphism
  (inputs [this] (->CartesianPower coll 2))
  (outputs [this] coll)

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this i] (func i))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive MagmaFunction :locus.base.logic.structure.protocols/set-function)