(ns locus.base.function.inclusion.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]))

; Inclusion functions
; Let A be a subset of B, then A and B together induce an inclusion function f: A to B whose
; surjective subobject is an identity function. It follows that f(a) = a for all a in A.
; Inclusion functions are a useful means of dealing with subobjects in the topos Sets, which
; is the most basic topos as it describes presheaves over a single point.
(deftype InclusionFunction [in out]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [in out]))

  Object
  (equals [this x]
    (and
      (instance? InclusionFunction x)
      (equal-universals? in (.in ^InclusionFunction x))
      (equal-universals? out (.out ^InclusionFunction x))))
  (toString [this]
    (str (str in) " ↪ " (str out)))

  clojure.lang.IFn
  (invoke [this obj] obj)
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(defmethod print-method InclusionFunction [^InclusionFunction v ^java.io.Writer w]
  (.write w (.toString v)))

(derive InclusionFunction :locus.base.logic.structure.protocols/inclusion-function)

(defmethod identity-function? InclusionFunction
  [func]

  (= (inputs func) (outputs func)))

; Special types of inclusion functions
(defn empty-inclusion-function
  [coll]

  (InclusionFunction. #{} coll))

; Complementation
(defmulti complement-inclusion-function type)

(defmethod complement-inclusion-function :locus.base.logic.structure.protocols/inclusion-function
  [func]

  (InclusionFunction.
    (difference (outputs func) (inputs func))
    (outputs func)))

(defmethod complement-inclusion-function :default
  [func]

  (inclusion-function
    (difference (outputs func) (inputs func))
    (outputs func)))