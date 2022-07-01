(ns locus.elementary.function.inclusion.identity
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]))

; Identity functions class
(deftype IdentityFunction [coll]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  Object
  (equals [this x]
    (and
      (instance? IdentityFunction x)
      (equal-universals? coll (.coll ^IdentityFunction x))))
  (toString [this]
    (str coll " ↪ " coll))

  clojure.lang.IFn
  (invoke [this obj] obj)
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(defmethod print-method IdentityFunction [^IdentityFunction v ^java.io.Writer w]
  (.write w (.toString v)))

(derive IdentityFunction :locus.elementary.function.core.protocols/identity-function)

(defmethod identity-function? IdentityFunction
  [func] true)
