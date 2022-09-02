(ns locus.elementary.cospan.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; Objects of the copresheaf topos Sets^{[2,1]}
; A cospan can be created by a pair of set functions with a common target set.
(deftype Cospan [a b c f g])

(defn cospan
  [f g]

  (let [a (inputs f)
        b (inputs g)
        c (outputs f)]
    (Cospan. a b c f g)))

; Cospan component sets
(defn first-cospan-source
  [^Cospan cospan]

  (.-a cospan))

(defn second-cospan-source
  [^Cospan cospan]

  (.-b cospan))

(defn cospan-target
  [^Cospan cospan]

  (.-c cospan))

; Cospan component functions
(defn first-cospan-function
  [cospan]

  (SetFunction. (.-a cospan) (.-c cospan) (.-f cospan)))

(defn second-cospan-function
  [cospan]

  (SetFunction. (.-b cospan) (.-c cospan) (.-g cospan)))

; First source properties
(defn apply-first-cospan-function
  [cospan x]

  ((first-cospan-function cospan) x))

; Second source properties
(defn apply-second-cospan-function
  [cospan x]

  ((second-cospan-function cospan) x))

; Cospan target properties
(defn first-fiber
  [cospan x]

  (fiber (first-cospan-function cospan) x))

(defn second-fiber
  [cospan x]

  (fiber (second-cospan-function cospan) x))

(defn fiber-pair
  [cospan x]

  (list
    (first-fiber cospan x)
    (second-fiber cospan x)))

(defn first-fiber-cardinality
  [cospan x]

  (count (first-fiber cospan x)))

(defn second-fiber-cardinality
  [cospan x]

  (count (second-fiber cospan x)))

(defn fiber-cardinality-pair
  [cospan x]

  (list
    (first-fiber-cardinality cospan x)
    (second-fiber-cardinality cospan x)))

; Cospan images and their union and intersection
(defn first-cospan-image
  [cospan]

  (function-image (first-cospan-function cospan)))

(defn second-cospan-image
  [cospan]

  (function-image (second-cospan-function cospan)))

(defn combined-image
  [cospan]

  (union
    (first-cospan-image cospan)
    (second-cospan-image cospan)))

(defn intersection-image
  [cospan]

  (intersection
    (first-cospan-image cospan)
    (second-cospan-image cospan)))

(defn combined-missing-targets
  [cospan]

  (difference
    (cospan-target cospan)
    (combined-image cospan)))

; Cospan image pairs
(defn cospan-images
  [cospan]

  (list
    (first-cospan-image cospan)
    (second-cospan-image cospan)))

(defn image-diset
  [cospan]

  (->Diset
    (first-cospan-image cospan)
    (second-cospan-image cospan)))

; Get the dual of a cospan copresheaf
(defn dual-cospan
  [^Cospan cospan]

  (cospan (.-g cospan) (.-f cospan)))

; Create a cospan copresheaf from a coproduct of two sets
(defn coproduct-cospan
  [a b]

  (let [coll (cartesian-coproduct a b)]
    (Cospan.
      a
      b
      coll
      (fn [x]
        (list 0 x))
      (fn [y]
        (list 1 y)))))

; Create a cospan by a partition of the input set of a function
(defn cospan-by-partition
  [func partition]

  (let [[a b] (seq partition)]
    (Cospan.
      a
      b
      (outputs func)
      (restrict-function func a)
      (restrict-function func b))))

; Products and coproducts in the topos of cospan copresheaves
(defn cospan-product
  [& cospans]

  (Cospan.
    (apply product (map first-cospan-source cospans))
    (apply product (map second-cospan-source cospans))
    (apply product (map cospan-target cospans))
    (apply product (map first-cospan-function cospans))
    (apply product (map second-cospan-function cospans))))

(defn cospan-coproduct
  [& cospans]

  (Cospan.
    (apply coproduct (map first-cospan-source cospans))
    (apply coproduct (map second-cospan-source cospans))
    (apply coproduct (map cospan-target cospans))
    (apply coproduct (map first-cospan-function cospans))
    (apply coproduct (map second-cospan-function cospans))))

(defmethod product Cospan
  [& cospans]

  (apply product cospans))

(defmethod coproduct Cospan
  [& cospans]

  (apply coproduct cospans))

; Subobjects in the topos of cospans
(defn subcospan
  [cospan new-first-source new-second-source new-target]

  (Cospan.
    new-first-source
    new-second-source
    new-target
    (first-cospan-function cospan)
    (second-cospan-function cospan)))

(defn restrict-first-source
  [cospan new-first-source]

  (Cospan.
    new-first-source
    (second-cospan-source cospan)
    (cospan-target cospan)
    (first-cospan-function cospan)
    (second-cospan-function cospan)))

(defn restrict-second-source
  [cospan new-second-source]

  (Cospan.
    (first-cospan-source cospan)
    new-second-source
    (cospan-target cospan)
    (first-cospan-function cospan)
    (second-cospan-function cospan)))

(defn subcospan?
  [cospan new-first-source new-second-source new-target]

  (let [fn1 (first-cospan-function cospan)
        fn2 (second-cospan-function cospan)]
    (and
      (superset? (set-image fn1 new-first-source) new-target)
      (superset? (set-image fn2 new-second-source) new-target))))

; Quotients in the topos of cospan copresheaves
(defn cospan-congruence?
  [cospan first-source-partition second-source-partition target-partition]

  (let [fn1 (first-cospan-function cospan)
        fn2 (second-cospan-function cospan)]
    (and
      (io-relation? fn1 first-source-partition target-partition)
      (io-relation? fn2 second-source-partition target-partition))))

(defn quotient-cospan
  [cospan first-source-partition second-source-partition target-partition]

  (let [fn1 (first-cospan-function cospan)
        fn2 (second-cospan-function cospan)]
    (cospan
      (quotient-function
        fn1
        first-source-partition
        target-partition)
      (quotient-function
        fn2
        second-source-partition
        target-partition))))

; Ontology of cospan copresheaves
(defn cospan?
  [func]

  (= (type func) Cospan))

(defn together-surjective-cospan?
  [func]

  (and
    (cospan? func)
    (let [[a b] (cospan-images func)
          combined-image (union a b)]
      (equal-universals? combined-image (cospan-target func)))))

(defn first-surjective-cospan?
  [cospan]

  (and
    (cospan? cospan)
    (equal-universals? (first-cospan-image cospan) (cospan-target cospan))))

(defn second-surjective-cospan?
  [cospan]

  (and
    (cospan? cospan)
    (equal-universals? (second-cospan-image cospan) (cospan-target cospan))))

(defn completely-surjective-cospan?
  [cospan]

  (and
    (cospan? cospan)
    (equal-universals? (first-cospan-image cospan) (cospan-target cospan))
    (equal-universals? (second-cospan-image cospan) (cospan-target cospan))))

; Disjointness conditions
(defn image-disjoint-cospan?
  [func]

  (and
    (cospan? func)
    (let [[a b] (cospan-images func)]
      (empty? (intersection a b)))))

(defn coproduct-cospan?
  [func]

  (and
    (cospan? func)
    (together-surjective-cospan? func)
    (image-disjoint-cospan? func)))

; Intersection and equality conditions on images
(defn image-intersecting-cospan?
  [func]

  (and
    (cospan? func)
    (let [[a b] (cospan-images func)]
      (not (empty? (intersection a b))))))

(defn image-equal-cospan?
  [func]

  (and
    (cospan? func)
    (let [[a b] (cospan-images func)]
      (equal-universals? a b))))

; Comparable images cospan
(defn comparable-images-cospan?
  [cospan]

  (and
    (cospan? cospan)
    (let [[a b] (cospan-images cospan)]
      (or
        (superset? (list a b))
        (superset? (list b a))))))