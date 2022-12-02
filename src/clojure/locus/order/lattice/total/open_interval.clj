(ns locus.order.lattice.total.open-interval
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.total.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import (locus.order.lattice.total.object TotallyOrderedSet)))

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







