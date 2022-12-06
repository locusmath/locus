(ns locus.algebra.semigroup.free.free-semigroup
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.term.signed-list :refer :all]
            [locus.algebra.group.term.signed-multiset :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; Every variety of semigroups is associated with a class of free semigroups. There are a number
; of different classes provided by us: free semigroups, free bands, free semilattices,
; free groups, and even free commutative groups. The later two also extend into our
; group theory subsystem.

; Free semigroups and free commutative semigroups
(defn free-monoid
  [coll]

  (->Monoid
    (->Universal
      (fn [seq]
        (and
          (seq? seq)
          (every?
           (fn [i]
             (coll i))
           seq))))
    (fn [[a b]]
      (concat a b))
    '()))

(defn free-commutative-monoid
  [coll]

  (->Monoid
    (->Universal
      (fn [multiset]
        (and
          (multiset? multiset)
          (every?
            (fn [i]
              (coll i))
            multiset))))
    (fn [[a b]]
      (add a b))
    (multiset '())))

; The free group consists entirely of signed lists
(defn free-group
  [coll]

  (->Group
    (->Universal
      (fn [signed-list]
        (and
          (signed-list? signed-list)
          (every?
            (fn [i]
              (coll i))
            (signed-list-values signed-list)))))
    (fn [[a b]]
      (concatenate-signed-lists a b))
    (->SignedList [] [])
    inv))

(defn free-commutative-group
  [coll]

  (->Group
    (->Universal
      (fn [signed-multiset]
        (and
          (signed-multiset? signed-multiset)
          (every?
            (fn [i]
              (coll i))
            (signed-support signed-multiset)))))
    (fn [[a b]]
      (add-signed-multisets a b))
    (->SignedMultiset {})
    inv))

; Free semilattices
(defn free-semilattice
  [coll]

  (->Semigroup
    (->Universal
      (fn [structure]
        (and
          (universal? structure)
          (every?
            (fn [i]
              (coll i))
            structure))))
    (fn [[a b]]
      (union a b))))

; Free semigroups
; In order to deal with the checks for duplicate terms
; it is most logical to use a vector based data structure
(defn duplicate-term?
  [coll start end]

  (let [len (- end start)
        [next-start next-end] [end (+ end len)]]
    (and
      (<= next-end (count coll))
      (=
       (subvec coll start end)
       (subvec coll next-start next-end)))))

(defn remove-subvec
  [coll start end]

  (into (subvec coll 0 start)
        (subvec coll end (count coll))))

(defn remove-duplicate-indices
  [coll start end]

  (remove-subvec coll start (+ start (* 2 (- end start)))))

; Duplicate finders
(defn find-duplicate-end-with-start
  [coll start]

  (let [len (count coll)]
    (loop [end (inc start)]
      (when (<= end len)
        (if (duplicate-term? coll start end)
          end
          (recur (inc end)))))))

(defn find-duplicate-indices
  [coll]

  (loop [i 0]
    (when (< i (count coll))
      (let [end (find-duplicate-end-with-start coll i)]
        (if (not (nil? end))
          [i end]
          (recur (inc i)))))))

(defn remove-duplicates
  [coll]

  (loop [current-coll coll]
    (let [current-indices (find-duplicate-indices current-coll)]
      (if (nil? current-indices)
        current-coll
        (recur
          (remove-duplicate-indices current-coll (first current-indices) (second current-indices)))))))

(defn band-concatenate
  [& colls]

  (remove-duplicates (vec (apply concat colls))))

(defn duplicate-free-vector?
  [coll]

  (and
    (vector? coll)
    (nil? (find-duplicate-indices coll))))

(defn duplicate-free-seq?
  [coll]

  (and
    (seq? coll)
    (duplicate-free-vector? (vec coll))))

(defn free-band
  [coll]

  (->Monoid
    (->Universal
      (fn [arg]
        (and
          (duplicate-free-vector? arg)
          (every?
            (fn [i]
              (coll i))
            arg))))
    (fn [[a b]]
      (band-concatenate a b))
    []))
