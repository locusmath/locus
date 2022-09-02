(ns locus.elementary.diset.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]))

; Disets are objects of the topos of pairs of sets Sets^2
; This topos is the topos of copresheaves over the discrete category
; with two objects and two identity morphisms. The subobjects, quotients,
; products, and quotients of Disets are defined by doubling up their
; their counterparts in Sets.

(deftype Diset [a b]
  StructuredDiset
  (first-set [this] a)
  (second-set [this] b)

  Object
  (toString [this]
    (str "*(" a " " b ")")))

(derive Diset :locus.elementary.function.core.protocols/diset)

(defmethod print-method Diset [^Diset v ^java.io.Writer w]
  (.write w (.toString v)))

; Get the underlying diset of a given structure
(defn diset
  ([obj]

   (if (or (vector? obj) (seq? obj))
     (Diset. (first obj) (second obj))
     (Diset. (first-set obj) (second-set obj))))
  ([a b]

   (Diset. a b)))

; Underlying diset
(defn underlying-diset
  [coll]

  (Diset.
    (first-set coll)
    (second-set coll)))

; The cardinality of a diset
(defn diset-cardinality
  [diset]

  (+ (count (first-set diset))
     (count (second-set diset))))

(defn diset-union
  [diset]

  (union (first-set diset) (second-set diset)))

(defn diset-intersection
  [diset]

  (intersection (first-set diset) (second-set diset)))

(defn cardinality-pair
  [diset]

  (list (count (first-set diset))
        (count (second-set diset))))

; Utility functions
(defn equal-diset
  [a]

  (Diset. a a))

(defn equal-singleton-diset
  [a]

  (Diset. #{a} #{a}))

(defn reverse-diset
  [coll]

  (Diset.
    (second-set coll)
    (first-set coll)))

; Products and coproducts in the topos of disets
(defn diset-product
  [& pairs]

  (Diset.
    (apply cartesian-product (map first-set pairs))
    (apply cartesian-product (map second-set pairs))))

(defn diset-coproduct
  [& pairs]

  (Diset.
    (apply cartesian-coproduct (map first-set pairs))
    (apply cartesian-coproduct (map second-set pairs))))

(defmethod product Diset
  [& args]

  (apply diset-product args))

(defmethod coproduct Diset
  [& args]

  (apply diset-coproduct args))

; Join and meet for disets themselves
(defn join-disets
  [& args]

  (Diset.
    (apply union (map first-set args))
    (apply union (map second-set args))))

(defn meet-disets
  [& args]

  (Diset.
    (apply intersection (map first-set args))
    (apply intersection (map second-set args))))

; Join and meet for set pairs instead of disets
(defn join-set-pairs
  [& args]

  (list
    (apply union (map first args))
    (apply union (map second args))))

(defn meet-set-pairs
  [& args]

  (list
    (apply intersection (map first args))
    (apply intersection (map second args))))

(defn join-set-pair-congruences
  [& args]

  (list
    (apply join-set-partitions (map first args))
    (apply join-set-partitions (map second args))))

(defn meet-set-pair-congruences
  [& args]

  (list
    (apply meet-set-partitions (map first args))
    (apply meet-set-partitions (map second args))))

; Operations for getting subobjects of disets
(defn restrict-first-set
  [pair a]

  (Diset. a (second-set pair)))

(defn restrict-second-set
  [pair b]

  (Diset. (first-set pair) b))

(defn disj-first-set
  [pair x]

  (Diset.
    (disj (first-set pair) x)
    (second-set pair)))

(defn disj-second
  [pair x]

  (Diset.
    (first-set pair)
    (disj (second-set pair) x)))

(defn subdiset
  [pair a b]

  (Diset. a b))

; Diset subalgebra lattices
(defn diset-subalgebras
  [pair]

  (set
    (cartesian-product
      (power-set (first-set pair))
      (power-set (second-set pair)))))

(defn seqable-diset-subalgebras
  [pair]

  (seqable-cartesian-product
    (seqable-power-set (first-set pair))
    (seqable-power-set (second-set pair))))

(defn subdisets
  [diset]

  (map
    (fn [[a b]]
      (Diset. a b))
    (diset-subalgebras diset)))

; Operations for getting quotients of disets
(defn quotient-diset
  [pair a b]

  (Diset. a b))

; Diset congruence lattices
(defn diset-congruences
  [coll]

  (set
    (cartesian-product
      (set-partitions (first-set coll))
      (set-partitions (second-set coll)))))

(defn seqable-diset-congruences
  [coll]

  (seqable-cartesian-product
    (set-partitions (first-set coll))
    (set-partitions (second-set coll))))

(defn quotient-disets
  [pair]

  (map
    (fn [[a b]]
      (Diset. a b))
    (diset-congruences pair)))

; The inclusion partial ordering on disets
(def superdiset?
  (assoc (->Universal
           (intersection
             seq?
             (fn [[a b]]
              (and
                (superset? (list (first-set a) (first-set b)))
                (superset? (list (second-set a) (second-set b)))))))
    :join join-disets
    :meet meet-disets
    :arities #{2}))

; Ontology of disets
; Classification of objects of the topos of pairs of sets
; which is the topos of set valued functors of the two
; object discrete category
(defn diset?
  [pair]

  (= (type pair) Diset))

(defn equal-cardinality-diset?
  [pair]

  (and
    (diset? pair)
    (= (count (first-set pair))
       (count (second-set pair)))))

(defn different-cardinality-diset?
  [pair]

  (and
    (diset? pair)
    (not= (count (first-set pair))
          (count (second-set pair)))))

(defn equal-diset?
  [pair]

  (and
    (diset? pair)
    (= (first-set pair) (second-set pair))))

(defn distance-one-diset?
  [pair]

  (and
    (diset? pair)
    (= (set-distance (first-set pair) (second-set pair)) 1)))

(defn distance-two-diset?
  [pair]

  (and
    (diset? pair)
    (= (set-distance (first-set pair) (second-set pair)) 2)))

(defn distance-three-diset?
  [pair]

  (and
    (diset? pair)
    (= (set-distance (first-set pair) (second-set pair)) 3)))

(defn distance-four-diset?
  [pair]

  (and
    (diset? pair)
    (= (set-distance (first-set pair) (second-set pair)) 4)))

(defn disjoint-diset?
  [pair]

  (and
    (diset? pair)
    (empty? (intersection (first-set pair) (second-set pair)))))

(defn nondisjoint-diset?
  [pair]

  (and
    (diset? pair)
    (not (empty? (intersection (first-set pair) (second-set pair))))))

(defn linear-diset?
  [pair]

  (and
    (diset? pair)
    (<= (count (intersection (first-set pair) (second-set pair))) 1)))

(defn max-intersection-count-two-diset?
  [pair]

  (and
    (diset? pair)
    (<= (count (intersection (first-set pair) (second-set pair))) 2)))

(defn max-intersection-count-three-diset?
  [pair]

  (and
    (diset? pair)
    (<= (count (intersection (first-set pair) (second-set pair))) 3)))

(defn max-intersection-count-four-diset?
  [pair]

  (and
    (diset? pair)
    (<= (count (intersection (first-set pair) (second-set pair))) 4)))

(defn inclusion-diset?
  [pair]

  (and
    (diset? pair)
    (superset? (list (first-set pair) (second-set pair)))))

(defn restriction-diset?
  [pair]

  (and
    (diset? pair)
    (superset? (list (second-set pair) (first-set pair)))))

(def comparable-diset?
  (union
    inclusion-diset?
    restriction-diset?))

(def covering-inclusion-diset?
  (intersection
    distance-one-diset?
    inclusion-diset?))

(def covering-restriction-diset?
  (intersection
    distance-one-diset?
    restriction-diset?))

(defn first-singleton-diset?
  [pair]

  (and
    (diset? pair)
    (singular-universal? (first-set pair))))

(defn second-singleton-diset?
  [pair]

  (and
    (diset? pair)
    (singular-universal? (second-set pair))))

(def element-diset?
  (intersection
    first-singleton-diset?
    inclusion-diset?))

(def singleton-diset?
  (intersection
    first-singleton-diset?
    second-singleton-diset?))

(def equal-singleton-diset?
  (intersection
    singleton-diset?
    equal-diset?))

; Ontology of the fundamental relations between disets
; Property ontology of objects of the topos of sets pairs
(defn !=diset
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= a b)))

(defn !=first-set
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (first-set a) (first-set b))))

(defn !=second-set
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (second-set a) (second-set b))))

(defn !=cardinality-pair
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (cardinality-pair a) (cardinality-pair b))))

(defn !=diset-cardinality
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (diset-cardinality a) (diset-cardinality b))))

(defn !=first-set-cardinality
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (count (first-set a)) (count (first-set b)))))

(defn !=second-set-cardinality
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (count (second-set a)) (count (second-set b)))))

(defn !=diset-distance
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (set-distance (first-set a) (second-set a))
          (set-distance (first-set b) (second-set b)))))

(defn !=diset-intersection-count
  [a b]

  (and
    (diset? a)
    (diset? b)
    (not= (count (intersection (first-set a) (second-set a)))
          (count (intersection (first-set b) (second-set b))))))




