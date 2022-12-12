(ns locus.set.mapping.function.optional.func
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (java.util Optional)))

; Consider the category of partial functions. Then a partial function is like a function that returns
; a java.util.Optional indicating rather or not it has a value or not. In the cases when it
; does not have a value it might return empty. Otherwise, it will return the appropriate value that
; under an optional wrapper. This allows you to embed the category of partial functions within
; the topos of Sets.

(deftype OptionalSet [coll]
  clojure.lang.Seqable
  (seq [this]
    (cons
      (Optional/empty)
      (map
        #(Optional/of %)
        coll)))

  clojure.lang.IFn
  (invoke [this]
    (and
      (= (type this) Optional)
      (or
        (not (.isPresent ^Optional this))
        (let [val (.get ^Optional this)]
          (coll val)))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive OptionalSet :locus.set.logic.core.set/universal)

(defn optional-set
  [coll]

  (->OptionalSet coll))

(defn present-values
  [coll]

  (if (= (type coll) OptionalSet)
    (.-coll ^OptionalSet coll)
    (set
      (for [i coll
            :when (.isPresent i)]
        (.get i)))))

; Optional functions theory
(defn optional-function
  [source target missing-input? func]

  (->SetFunction
    (optional-set source)
    (optional-set target)
    (fn [^Optional x]
      (if (.isPresent x)
        (let [v (.get x)]
          (if (missing-input? x)
            (Optional/empty)
            (Optional/of (func x))))
        (Optional/empty)))))

(defn optional-endofunction
  [source missing-input? func]

  (optional-function source source missing-input? func))

(defn present-inputs
  [optional-function]

  (set
    (for [i (inputs optional-function)
          :when (and
                  (.isPresent i)
                  (.isPresent (optional-function i)))
          :let [val (.get i)]]
      val)))

(defn total-component-function
  [optional-function]

  (->SetFunction
    (present-inputs optional-function)
    (present-values (outputs optional-function))
    (fn [val]
      (.get ^Optional (optional-function (Optional/of val))))))