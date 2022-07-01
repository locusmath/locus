(ns locus.elementary.function.inclusion.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]))

; Inclusion functions
(deftype InclusionFunction [in out]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  StructuredDiset
  (first-set [this] in)
  (second-set [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

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

(derive InclusionFunction :locus.elementary.function.core.protocols/inclusion-function)

(defmethod identity-function? InclusionFunction
  [func]

  (= (inputs func) (outputs func)))

; Complementation
(defmulti complement-inclusion-function type)

(defmethod complement-inclusion-function :locus.elementary.function.core.protocols/inclusion-function
  [func]

  (InclusionFunction.
    (difference (outputs func) (inputs func))
    (outputs func)))

(defmethod complement-inclusion-function :default
  [func]

  (inclusion-function
    (difference (outputs func) (inputs func))
    (outputs func)))