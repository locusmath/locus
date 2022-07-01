(ns locus.elementary.bijection.enum.impl
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.bijection.core.object Bijection)))

; Create a bijection that enumerates the elements of some list
(defn enumeration-bijection
  [coll]

  (Bijection.
    (->Upto (count coll))
    (set coll)
    (fn [x]
      (nth coll x))
    (fn [y]
      (.indexOf coll y))))

; A range can be treated like an enumeration bijection
(defn range-enumeration
  [x y]

  (let [dist (int (Math/abs (- x y)))]
    (Bijection.
      (->Upto dist)
      (seqable-interval x y)
      (fn [i]
        (+ i x))
      (fn [a]
        (- a x)))))

