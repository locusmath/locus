(ns locus.elementary.function.multiplicity.func
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.nms :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.util :refer :all]))

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