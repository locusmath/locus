(ns locus.base.function.multiplicity.func
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.numeric.nms :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; A multiplicity function is a function from a set to some
; set of counting numbers, where each output value represents the
; multiplicity of the element in the collection

; Get a multiplicity function from a multiset or other collection
(defn multiplicity-function
  [coll]

  (SetFunction.
    (set coll)
    (set
      (map
        (partial multiplicity coll)
        (set coll)))
    (fn [i]
      (multiplicity coll i))))

; Multiplicity functions
(defn multiplicity-function?
  [func]

  (and
    (set-function? func)
    (every? natural-number? (function-image func))))

(def injective-multiplicity-function?
  (intersection
    multiplicity-function?
    injective?))

(def constant-multiplicity-function?
  (intersection
    multiplicity-function?
    constant-function?))

(defn simple-multiplicity-function?
  [func]

  (and
    (set-function? func)
    (every?
      (fn [input]
        (= 1 (func input)))
      (inputs func))))