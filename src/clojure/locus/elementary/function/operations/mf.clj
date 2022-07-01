(ns locus.elementary.function.operations.mf
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]))

; A data type for describing magma functions
(deftype MagmaFunction [coll func]
  ConcreteMorphism
  (inputs [this] (->CompleteRelation coll))
  (outputs [this] coll)

  AbstractMorphism
  (source-object [this] (inputs this))
  (target-object [this] (outputs this))

  StructuredDiset
  (first-set [this] (inputs this))
  (second-set [this] (outputs this))

  clojure.lang.IFn
  (invoke [this i] (func i))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive MagmaFunction :locus.elementary.function.core.protocols/identity-function)