(ns locus.grothendieck.topology.metric.pseudometric
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.grothendieck.topology.metric.object :refer :all]))

; Every function from a set to a metric space produces an induced pseudometric
; on its domain. In particular, this is applicable to short maps in the category
; of metric spaces. Consequently, the categorical theory of distance is most
; naturally expressed in terms of pseudometrics rather then metrics.
(deftype Pseudometric [coll distance]
  ConcreteObject
  (underlying-set [this] coll))

(derive Pseudometric :locus.elementary.function.core.protocols/structured-set)

; The key property that distinguishes pseudometrics from metrics is that we can
; get them induced by any function from a set to a metric space.
(defn induced-pseudometric
  [source-set target-metric func]

  (Pseudometric.
    source-set
    (fn [x y]
      (distance target-metric (func x) (func y)))))

; A notable property of pseudometrics is that they can be used to describe
; the dual of the lattice of partitions of a set. This lattice is naturally
; associated to the lattice of subsets in the topos of sets.
(defn equivalence-pseudometric
  [rel]

  (Pseudometric.
    (vertices rel)
    (fn [x y]
      (if (rel (list x y)) 0 1))))

(defn partition-pseudometric
  [family]

  (Pseudometric.
    (dimembers family)
    (fn [x y]
      (if (= (projection family x) (projection family y)) 0 1))))

; Test for equality and get equal components of pseudometrics
(defn pseudometric-equality
  [metric]

  (->Universal
    (fn [[a b]]
      (zero? (distance metric a b)))))

(defn equal-component-of
  [metric x]

  (set
    (filter
      (fn [i]
        (zero? (distance metric i x)))
      (underlying-set metric))))

(defn equal-components
  [metric]

  (let [coll (underlying-set metric)]
    (set
      (loop [remaining-elements coll
             rval #{}]
        (if (empty? remaining-elements)
          rval
          (let [next-element (first remaining-elements)
                next-component (equal-component-of metric next-element)]
            (recur
              (difference remaining-elements next-component)
              (conj rval next-component))))))))

; Get the distance between components of a real vector space as a pseudometric
(defn component-distance
  [n i]

  (Pseudometric.
    (real-vector-space n)
    (fn [x y]
      (let [d (- (nth x i) (nth y i))]
        (if (neg? d) (- d) d)))))




