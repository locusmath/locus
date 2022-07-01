(ns locus.elementary.order.total.open-interval
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.order.total.object :refer :all])
  (:import (locus.elementary.order.total.object TotallyOrderedSet)))

; Let T be a total order, then every open set of T in its order topology is the union
; of a set of open sets consisting of either the entire set T, a lower directed
; open ray, an upper directed open ray, or an open interval. In other words,
; the generators for the order topology are like open intervals with optional
; upper and lower bounds. We therefore generalize these different types of
; open sets to the convex open set class.
(deftype ConvexOpenSet [order lower-bounds upper-bounds]
  clojure.lang.IFn
  (invoke [this obj]
    (let [rel (underlying-relation order)]
      (and
        ((underlying-set order) obj)
        (or
          (empty? lower-bounds)
          (let [lower-bound (first lower-bounds)]
            (rel (list lower-bound obj))))
        (or
          (empty? upper-bounds)
          (let [upper-bound (first upper-bounds)]
            (rel (list obj upper-bound)))))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defn open-interval
  [order a b]

  (ConvexOpenSet. order #{a} #{b}))







