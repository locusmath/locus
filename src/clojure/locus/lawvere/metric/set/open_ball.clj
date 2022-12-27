(ns locus.lawvere.metric.set.open-ball
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.lawvere.metric.core.object :refer :all]))

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

