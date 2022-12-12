(ns locus.set.copresheaf.incidence.system.multifamily
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.copresheaf.incidence.system.family :refer :all])
  (:import [locus.set.logic.core.set Universal]))

; We call a set system a family of sets. So by generalizing, we say
; that a multiset of sets is a multifamily. These emerge for example, from
; the basic theory of incidence structures as well as from the
; sets of output sets of binary relations and set valued functions.

; Multifamilies
(defn multifamily
  [coll]

  (multiset (map set coll)))

; progression families
(defn progression-partition
  [coll]

  (if (empty? coll)
    #{}
    (let [current-support (support coll)]
      (conj
       (progression-partition (multiset-difference coll current-support))
       current-support))))

; Multifamilies that emerge from preordering relations. Every multifamily
; can be created from the maximal proper subdimembers
(defn suprema-representations
  "Suprema irreducible subdimembers"
  [family]

  (let [dimembers (apply union family)]
    (multiset
     (map
      (fn [i]
        (intersection
         (suprema-irreducible-dimembers family)
         (subdimembers family i)))
      dimembers))))

(defn maximal-proper-subdimember-sets
  [family]

  (multiset
   (map
    (fn [i]
      (disj (subdimembers family i) i))
    (maximal-dimembers family))))

(defn proper-subdimember-sets
  [family]

  (multiset
   (map
    (fn [i]
      (disj (subdimembers family i) i))
    (apply union family))))

(defn subdimember-sets
  [family]

  (multiset
   (map
    (fn [i]
      (subdimembers family i))
    (apply union family))))

; Adjacencies sets are especially associated with symmetric
; binary relations and their output sets.
(defn adjacencies-sets
  [family]

  (multiset
   (map
    (fn [i]
      (adjacencies family i))
    (apply union family))))

(defn proper-adjacencies-sets
  [family]

  (multiset
   (map
    (fn [i]
      (disj (adjacencies family i) i))
    (apply union family))))

; Pair degrees
; The idea of the degrees of vertices of a set system can naturally be 
; generalized to the degrees of subsets of the set system which leads
; to the theory of pair degrees.
(defn parent-counts
  [family child-sets]

  (apply
     add
     (map
      (fn [coll]
        (repeat-multiset
         (count
          (supermembers family coll))
         coll))
      child-sets)))

(defn child-degrees
  [family]

  (parent-counts family (cl subclass-closed? family)))

(defn singleton-degrees
  [family]

  (parent-counts family (unary-family (apply union family))))

(defn pair-degrees
  [family]

  (parent-counts
   family
   (selections (apply union family) 2)))

; Ontology of multifamilies
; The classification of multifamilies can proceed in a number of ways
; including the examination of the set theoretic properties of the
; multifamily and its properties as a multiset. We will start with
; its properties as a multiset.
(defn multifamily?
  [coll]

  (and
   (multiset? coll)
   (every? universal? coll)))

(def size-two-multifamily?
  (intersection
   size-two-multiset?
   multifamily?))

(def size-three-multifamily?
  (intersection
   size-three-multiset?
   multifamily?))

(def size-four-multifamily?
  (intersection
   size-four-multiset?
   multifamily?))

(def equal-multifamily?
  (intersection
   equal-multiset?
   multifamily?))

(def size-two-equal-multifamily?
  (intersection
   multifamily?
   size-two-equal-multiset?))

(def size-three-equal-multifamily?
  (intersection
   multifamily?
   size-three-equal-multiset?))

(def size-four-equal-multifamily?
  (intersection
   multifamily?
   size-four-equal-multiset?))

(defn near-family?
  [coll]

  (and
   (near-universal? coll)
   (every? universal? coll)))

(def regular-multifamily?
  (intersection
   regular-multiset?
   multifamily?))

(def kuratowski-pair-multifamily?
  (intersection
   kuratowski-pair-multiset?
   multifamily?))

; Classification of multifamilies by member cardinalities
(defn nullfree-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= 1 (count i)))
     coll)))

(defn rank-one-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= (count i) 1))
     coll)))

(defn rank-two-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= (count i) 2))
     coll)))

(defn singleton-free-rank-two-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (or (= (count i) 0) (= (count i) 2)))
     coll)))

(defn nullfree-rank-two-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= 1 (count i) 2))
     coll)))

(defn rank-three-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= (count i) 3))
     coll)))

(defn rank-four-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (<= (count i) 4))
     coll)))

(defn unary-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (= (count i) 1))
     coll)))

(defn binary-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (= (count i) 2))
     coll)))

(defn ternary-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (= (count i) 2))
     coll)))

(defn quaternary-multifamily?
  [coll]

  (and
   (multiset? coll)
   (every?
     (fn [i]
       (= (count i) 2))
     coll)))

; Uniform multifamilies
(defn uniform-multifamily?
  [coll]

  (and
   (multifamily? coll)
   (equal-seq? (map count coll))))

; Multisets of edges
(defn symmetric-edges-multifamily?
  "Loop unique and pair degree less then or equal to two."
  [coll]

  (and
   (nullfree-rank-two-multifamily? coll)
   (every?
    (fn [i]
      (or
       (and (singular-universal? i) (= (multiplicity coll i) 1))
       (and (size-two-universal? i) (= (multiplicity coll i) 2))))
    (set coll))))

; Classes of multifamilies by underlying family
(defn power-multifamily?
  [coll]

  (and
   (multiset? coll)
   (power-set? (set coll))))

(defn preorder-containment-multifamily?
  [coll]

  (and
   (multiset? coll)
   (preorder-containment-family? (set coll))))

(defn chain-multifamily?
  [coll]

  (and
   (multiset? coll)
   (chain-family? (set coll))))

(defn nullfree-chain-multifamily?
  [coll]

  (and
   (multiset? coll)
   (nullfree-chain-family? (set coll))))

(defn sperner-multifamily?
  [coll]

  (and
   (multiset? coll)
   (sperner-family? (set coll))))

(defn nullfree-sperner-multifamily?
  [coll]

  (and
   (multiset? coll)
   (nullfree-sperner-family? (set coll))))


