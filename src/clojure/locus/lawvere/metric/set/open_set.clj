(ns locus.lawvere.metric.set.open-set
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.lawvere.metric.core.object :refer :all]
            [locus.lawvere.metric.set.open-ball :refer :all]))

; We can construct an open set in the metric topology of a metric space, by
; defining some kind of collection of open balls. This class handles the data
; of such collections of open balls, so that we can construct the metric topology.
(deftype MetricOpenSet [space balls]
  ConcreteObject
  (underlying-set [this] this)

  clojure.lang.IFn
  (invoke [this arg]
    (and
      ((underlying-set space) arg)
      (every?
        (fn [ball]
          (ball arg))
        balls)))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(defmethod union* MetricOpenSet
  [^MetricOpenSet a, ^MetricOpenSet b]

  (MetricOpenSet. (.space a) (union (.balls a) (.balls b))))

(defn open-set-of-metric?
  [metric open]

  (and
    (= (type open) MetricOpenSet)
    (= (.space open) metric)))
