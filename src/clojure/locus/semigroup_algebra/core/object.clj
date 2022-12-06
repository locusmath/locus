(ns locus.semigroup-algebra.core.object
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.free.free-semigroup :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.module.vector.rset :refer :all])
  (:import (locus.algebra.semigroup.monoid.object Monoid)
           (locus.algebra.semigroup.core.object Semigroup)
           (locus.algebra.group.core.object Group))
  (:use (clojure.walk)))

; Semigroup ring elements
; These are ringed sets of semigroup elements
(deftype SemigroupRingElement [ring semigroup data]
  RingedSet
  (ring-of-coefficients [this] ring)
  (terms [this] (keys data))
  (coefficient [this arg] (get data arg)))

(def ex
  (SemigroupRingElement.
    zz
    (free-commutative-monoid #{0 1 2})
    {(multiset '(0 0)) -2
     (multiset '(1 1)) 3}))

; Arithmetical properties of semigroup ring elements
(defmethod negate SemigroupRingElement
  [^SemigroupRingElement elem]

  (SemigroupRingElement.
    (.ring elem)
    (.semigroup elem)
    (clojure.walk/walk
      (fn [[k v]]
        [k ((.inv (additive-semigroup (.ring elem))) v)])
      identity
      (.data elem))))

(defn add-rs-maps
  [r s a b]

  (let [coll (union (set (keys a))
                    (set (keys b)))
        add (additive-semigroup r)]
    (zipmap
      coll
      (map
        (fn [key]
          (let [aval (get a key)
                bval (get b key)]
            (cond
              (nil? aval) bval
              (nil? bval) aval
              :else (add [aval bval]))))
        coll))))

(defmethod add [SemigroupRingElement SemigroupRingElement]
  [^SemigroupRingElement elem1, ^SemigroupRingElement elem2]

  (let [r (.ring elem1)
        s (.semigroup elem1)
        a (.data elem1)
        b (.data elem2)]
    (SemigroupRingElement.
      r
      s
      (add-rs-maps r s a b))))

(defn multiply-rs-terms
  [r s [s1 r1] [s2 r2]]

  (let [rmul (multiplicative-semigroup r)]
    (hash-map
      (s [s1 s2])
      (rmul [r1 r2]))))

(defmethod multiply [SemigroupRingElement SemigroupRingElement]
  [^SemigroupRingElement elem1, ^SemigroupRingElement elem2]

  (let [r (.ring elem1)
        s (.semigroup elem1)
        a (.data elem1)
        b (.data elem2)]
    (SemigroupRingElement.
      r
      s
      (let [coll (cartesian-product (set a) (set b))]
        (reduce
          (partial add-rs-maps r s)
          (map
            (fn [[[s1 r1] [s2 r2]]]
              (multiply-rs-terms r s [s1 r1] [s2 r2]))
            coll))))))

; Additive identities
(defn zero-semigroup-ring-element
  [ring semigroup]

  (SemigroupRingElement.
    ring
    semigroup
    {}))

(defn semigroup-algebra-classifier
  [ring semigroup]

  (let [ring-elements (underlying-set ring)
        semigroup-elements (underlying-set semigroup)
        is-seqable? (and (seqable-universal? ring-elements)
                         (seqable-universal? semigroup-elements))]
    (if is-seqable?
      (->SeqableUniversal
        (fn [elem]
          (and
            (= (type elem) SemigroupRingElement)
            (= (.ring elem) ring)
            (= (.semigroup elem) semigroup)))
        (map
          (fn [data]
            (SemigroupRingElement. ring semigroup data))
          (seqable-partial-mappings
            (set semigroup-elements)
            (disj (set ring-elements) (identity-element (additive-semigroup ring)))))
        {})
      (->Universal
        (fn [elem]
         (and
           (= (type elem) SemigroupRingElement)
           (= (.ring elem) ring)
           (= (.semigroup elem) semigroup)))))))

(defn semigroup-algebra
  [ring semigroup]

  (let [classifier (semigroup-algebra-classifier ring semigroup)]
    (make-ring
      (if (intrinsic-ring? ring)
        (Group.
          classifier
          (fn [[a b]]
            (+ a b))
          (zero-semigroup-ring-element ring semigroup)
          (fn [a]
            (- a)))
        (Monoid.
          classifier
          (fn [[a b]]
            (+ a b))
          (zero-semigroup-ring-element ring semigroup)))
      (Semigroup.
        classifier
        (fn [[a b]]
          (* a b))))))

(defmethod get-semiring SemigroupRingElement
  [^SemigroupRingElement elem]

  (semigroup-algebra (.ring elem) (.semigroup elem)))

; Mathematical manipulation of familiar data structures
(defn multiply-multirelations
  [r1 r2]

  (apply
    add
    (map
      (fn [[i j]]
        (->Multiset {(seq (concat i j)) (* (multiplicity r1 i) (multiplicity r2 j))}))
      (cartesian-product (support r1) (support r2)))))

(defn multiply-multiclans
  [r1 r2]

  (apply
    add
    (map
      (fn [[i j]]
        (->Multiset {(add i j) (* (multiplicity r1 i) (multiplicity r2 j))}))
      (cartesian-product (support r1) (support r2)))))








