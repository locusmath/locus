(ns locus.set.mapping.function.operations.mf
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.limit.power :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]))

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

(derive MagmaFunction :locus.set.logic.structure.protocols/set-function)