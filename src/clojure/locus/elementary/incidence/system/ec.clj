(ns locus.elementary.incidence.system.ec
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all])
  (:import [locus.elementary.logic.base.core Universal]))

; An egalitarian clan is simply a clan whose elements are all equal multisets, meaning that all
; of their elements are equal. This is distinguished from an equal multiclan which doesn't
; necessarily need to be egalitarian.

; Support degrees
(def support-degrees
  (comp degrees (partial umap support)))

(defn membership-signature
  [coll elem]

  (multiset
   (for [i coll
         :when (contains? (support i) elem)]
     (multiplicity i elem))))

(defn membership-signatures
  [coll]

  (umap
   (partial membership-signature coll)
   (apply union (map support coll))))

; Egalitarian multiclans
(defn egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? equal-multiset? coll)))

(def equal-egalitarian-multiclan?
  (intersection
   egalitarian-multiclan?
   equal-multiset?))

(def egalitarian-clan?
  (intersection
   egalitarian-multiclan?
   universal?))

; Cardinality restricted examples
(defn nullfree-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? (intersection equal-multiset? nonempty-multiset?) coll)))

(defn rank-two-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-two-equal-multiset? coll)))

(defn rank-three-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-three-equal-multiset? coll)))

(defn rank-four-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-four-equal-multiset? coll)))

; Uniform strictly equal multiclans
(defn uniform-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (or (= (count coll) 0)
       (apply = (map count coll)))))

(defn binary-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-two-equal-multiset? coll)))

(defn ternary-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-three-equal-multiset? coll)))

(defn quaternary-egalitarian-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-four-equal-multiset? coll)))

; Cardinality distinct egalitarian clans
(defn cardinality-distinct-egalitarian-clan?
  [coll]

  (and
   (egalitarian-clan? coll)
   (or
    (empty? coll)
    (distinct? (map count coll)))))
