(ns locus.set.mapping.invertible.enum.impl
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.invertible.function.object :refer :all]))

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