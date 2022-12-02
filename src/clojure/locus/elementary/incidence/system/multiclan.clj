(ns locus.elementary.incidence.system.multiclan
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.vertexset :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.multifamily :refer :all]
            [locus.elementary.incidence.system.ec :refer :all]
            [locus.elementary.incidence.system.clan :refer :all]))

; A set of multisets we call a clan. So by generalizing we call a multiset of multisets
; a multiclan. By calling them this, we follow a consistent terminology.

; Classification of multiclans by their signatures
(defn multiclan
  [coll]

  (multiset (map multiset coll)))

(defn multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? multiset? coll)))

(def regular-multiclan?
  (intersection
   multiclan?
   regular-multiset?))

(def kuratowski-pair-multiclan?
  (intersection
   multiclan?
   kuratowski-pair-multiset?))

(def near-clan?
  (intersection
   multiclan?
   near-universal?))

(def equal-multiclan?
  (intersection
   multiclan?
   equal-multiset?))

(def size-two-multiclan?
  (intersection
   multiclan?
   size-two-multiset?))

(def size-three-multiclan?
  (intersection
   multiclan?
   size-three-multiset?))

(def size-four-multiclan?
  (intersection
   multiclan?
   size-four-multiset?))

(def size-two-equal-multiclan?
  (intersection
   multiclan?
   size-two-equal-multiset?))

(def size-three-equal-multiclan?
  (intersection
   multiclan?
   size-three-equal-multiset?))

(def size-four-equal-multiclan?
  (intersection
   multiclan?
   size-four-equal-multiset?))

; Classification of multiclans by member signatures
(defn kuratowski-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? kuratowski-pair-multiset? coll)))

(defn nullfree-multiclan?
  [coll]

  (and
   (multiclan? coll)
   (every? (fn [i] (<= 1 (count i))) coll)))

(defn irreflexive-kuratowski-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? order-two-kuratowski-pair-multiset? coll)))

(defn rank-two-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-two-multiset? coll)))

(defn rank-three-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-three-multiset? coll)))

(defn rank-four-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? max-size-four-multiset? coll)))

(defn binary-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-two-multiset? coll)))

(defn ternary-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-three-multiset? coll)))

(defn quaternary-multiclan?
  [coll]

  (and
   (multiset? coll)
   (every? size-four-multiset? coll)))

; We need to also be able to reason about chains of multisets
(defn multiset-partial-sums
  [& coll]

  (multiset
    (map
     (fn [i]
       (apply add (take i coll)))
     (range 1 (inc (count coll))))))

(defn consecutive-multiset-differences
  [coll]

  (let [sorted-coll (sort
                      (fn [a b]
                        (< (count a) (count b)))
                      (seq coll))]
    (map
      (fn [i]
        (if (zero? i)
          (first sorted-coll)
          (multiset-difference
            (nth sorted-coll i)
            (nth sorted-coll (dec i)))))
      (range (count coll)))))

(defn chain-multiclan?
  [coll]

  (and
    (multiset? coll)
    (chain-clan? (set coll))))

; Extra properties to classify multiclan by 
(defn set-uniform-multiclan?
  [coll]

  (support-uniform-clan? (set coll)))

(defn uniform-multiclan?
  [coll]

  (and
   (multiclan? coll)
   (equal-seq? (map count coll))))
