(ns locus.grothendieck.topology.metric.open-ball
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.grothendieck.topology.metric.object :refer :all]))

; Let M be a metric space, and x a point of M then we define the open ball
; M(x,r) to be the set of all elements that are a distance less then the
; radius r from the point x. We use these open balls as generators
; for the metric topology of a metric space.
(deftype OpenBall [space point radius]
  ConcreteObject
  (underlying-set [this] this)

  clojure.lang.IFn
  (invoke [this arg]
    (and
      ((underlying-set space) arg)
      (or
        (= radius ##Inf)
        (let [d (distance space point arg)]
         (< d radius)))))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

