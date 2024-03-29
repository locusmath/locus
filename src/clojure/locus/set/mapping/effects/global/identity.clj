(ns locus.set.mapping.effects.global.identity
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]))

; Identity functions class
(deftype IdentityFunction [coll]
  AbstractMorphism
  (source-object [this] coll)
  (target-object [this] coll)

  ConcreteMorphism
  (inputs [this] coll)
  (outputs [this] coll)

  ConcreteObject
  (underlying-set [this] (->CartesianProduct [coll coll]))

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

(derive IdentityFunction :locus.set.logic.structure.protocols/identity-function)

(defmethod identity-function? IdentityFunction
  [func] true)

