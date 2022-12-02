(ns locus.distance.lawvere.metric
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.category.core.object :refer :all]))

; Categories can be seen as intuitive abstractions of motion and of change. A morphism f: A -> B
; is a change from one point A to another point B, in either space or time. Categories are
; the best means we have of modeling change. How fitting then that distance should be modeled
; by categories. Distances describe a property of a motion f: A -> B from a point A to another
; point B. To describe distances categorically, we can establish a hom number to each motion
; of a hom class.

; The generally accepted way of describing distances categorically was provided by Lawvere.
; A Lawvere metric is a category enriched over the monoidal category of the extended
; real numbers with addition and its usual ordering. The result are Lawvere metrics, which
; are extended pseudoquasimetrics. The more familiar types of metric spaces have to be
; introduced as special cases and so predicates are defined to deal with them.

(deftype LawvereMetric [coll distance]
  ConcreteObject
  (underlying-set [this] coll)

  StructuredDiset
  (first-set [this] (->CompleteRelation coll))
  (second-set [this] coll)

  StructuredQuiver
  (underlying-quiver [this] (complete-relational-quiver coll))
  (source-fn [this] first)
  (target-fn [this] second)
  (transition [this e] e)

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (complete-relational-unital-quiver coll))
  (identity-morphism-of [this obj] (list obj obj))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms this))

  clojure.lang.IFn
  (invoke [this [[a b] [c d]]] (list c b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive LawvereMetric :locus.elementary.copresheaf.core.protocols/structured-category)

; Get the underlying relations and multirelations of lawvere metrics
(defmethod underlying-relation LawvereMetric
  [^LawvereMetric metric] (morphisms metric))

(defmethod underlying-multirelation LawvereMetric
  [^LawvereMetric metric] (underlying-relation metric))

(defmethod visualize LawvereMetric
  [^LawvereMetric metric] (visualize (underlying-relation metric)))

; Get the distance between two points in a metric space
(defmulti distance (fn [metric a b] (type metric)))

(defmethod distance LawvereMetric
  [^LawvereMetric metric, a, b]

  ((.distance metric) a b))

; Get the hom number in a distance enriched category
(defn hom-number
  [metric morphism]

  (distance metric (first morphism) (second morphism)))

; The discrete metric is a rather simple example in metric space theory
(defn discrete-metric
  [coll]

  (LawvereMetric.
    coll
    (fn [x y]
      (if (= x y) 0 1))))

; A notable property of pseudometrics is that they can be used to describe
; the dual of the lattice of partitions of a set. This lattice is naturally
; associated to the lattice of congruences of a set.
(defn equivalence-pseudometric
  [rel]

  (LawvereMetric.
    (vertices rel)
    (fn [x y]
      (if (rel (list x y))
        0
        1))))

(defn partition-pseudometric
  [family]

  (LawvereMetric.
    (dimembers family)
    (fn [x y]
      (if (= (projection family x) (projection family y))
        0
        1))))

; The equivalence properties of pseudometrics can also be applied in the
; other direction so that we can get for a given pseudometric an equivalence
; relation associated to it.
(defn metric-equal?
  [metric a b]

  (zero? (distance metric a b)))

(defn metric-equality
  [metric]

  (->Universal
    (fn [[a b]]
      (metric-equal? metric a b))))

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

; Every mapping from a set S to a lawvere metric space is going to provide an induced
; metric defined by distance between values of S under the mapping. This is the
; induced metric of the space.
(defn induced-metric
  [source-set target-metric func]

  (LawvereMetric.
    source-set
    (fn [x y]
      (distance target-metric (func x) (func y)))))

; The class of metric spaces is naturally partially ordered by distance, so that
; metrics with larger distances between each of their pairs of points are larger
; than one another. This metric is the fundamental partial order upon which
; the category of metric spaces and short maps is derived.
(defn submetric?
  [a b]

  (let [a-elements (underlying-set a)
        b-elements (underlying-set b)]
    (and
      (equal-universals? a-elements b-elements)
      (every?
        (fn [[x y]]
          (<= (distance a x y)
              (distance b x y)))
        (cartesian-power a-elements 2)))))

; Create a space of real vectors to be used with various metrics
(defn real-vector-space
  [n]

  (->Universal
    (fn [coll]
      (and
        (vector? coll)
        (= (count coll) n)
        (every? real-number? coll)))))

; The most common metric space
(defn euclidean-metric-space
  [n]

  (LawvereMetric.
    (real-vector-space n)
    (fn [x y]
      (Math/sqrt
        (apply
          +
          (map
            (fn [i]
              (let [d (- (nth x i) (nth y i))]
                (* d d)))
            (range n)))))))

; The taxicab metric is another kind of metric on the real numbers
(defn taxicab-metric
  [n]

  (LawvereMetric.
    (real-vector-space n)
    (fn [x y]
      (apply
        +
        (map
          (fn [i]
            (let [d (- (nth x n) (nth y n))]
              (if (neg? d) (- d) d)))
          (range n))))))

; Get the chebyshev metric on affine space
(defn chebyshev-metric
  [n]

  (LawvereMetric.
    (real-vector-space n)
    (fn [x y]
      (apply
        max
        (map
          (fn [i]
            (let [d (- (nth x n) (nth y n))]
              (if (neg? d) (- d) d)))
          (range n))))))

; One dimensional and two dimensional euclidean spaces have corresponding
; apache commons math geometry
(def one-dimensional-euclidean-space
  (euclidean-metric-space 1))

(def two-dimensional-euclidean-space
  (euclidean-metric-space 2))

(def three-dimensional-euclidean-space
  (euclidean-metric-space 3))

; Get the distance between components of a real vector space as a pseudometric
(defn component-distance
  [n i]

  (LawvereMetric.
    (real-vector-space n)
    (fn [x y]
      (let [d (- (nth x i) (nth y i))]
        (if (neg? d) (- d) d)))))

; The sequence of all distances produced by the metric.
(defn all-distances
  [metric]

  (seq
    (map
      (fn [[a b]]
        (distance metric a b))
      (cartesian-power (underlying-set metric) 2))))

; Ontology of metrically enriched categories
(defn lawvere-metric?
  [metric]

  (= (type metric) LawvereMetric))

(defn pseudoquasimetric?
  [metric]

  (and
    (lawvere-metric? metric)
    (every?
      (fn [i]
        (not= i ##Inf))
      (all-distances metric))))

(defn pseudometric?
  [metric]

  (and
    (pseudoquasimetric? metric)
    (every?
      (fn [[a b]]
        (= (distance metric a b)
           (distance metric b a)))
      (cartesian-power (underlying-set metric) 2))))

(defn quasimetric?
  [metric]

  (and
    (pseudoquasimetric? metric)
    (every?
      (fn [[a b]]
        (or
          (= a b)
          (not= (distance metric a b) 0)))
      (cartesian-power (underlying-set metric) 2))))

(defn metric?
  [metric]

  (and
    (pseudoquasimetric? metric)
    (every?
      (fn [[a b]]
        (and
          (= (distance metric a b) (distance metric b a))
          (or
            (= a b)
            (not= (distance metric a b) 0))))
      (cartesian-power (underlying-set metric) 2))))
