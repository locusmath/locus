(ns locus.base.invertible.enum.impl
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.invertible.function.object :refer :all]))

; Create a bijection that enumerates the elements of some list
(defn invertible-enumeration-function
  [coll]

  (->InvertibleFunction
    (->Upto (count coll))
    (set coll)
    (fn [x]
      (nth coll x))
    (fn [y]
      (.indexOf coll y))))

; A range can be treated like an enumeration bijection
(defn invertible-range-function
  [x y]

  (let [dist (int (Math/abs (- x y)))]
    (->InvertibleFunction
      (->Upto dist)
      (->RangeSet x y)
      (fn [i]
        (+ i x))
      (fn [a]
        (- a x)))))