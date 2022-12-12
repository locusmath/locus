(ns locus.set.tree.cospan.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Objects of the copresheaf topos Sets^{[2,1]}
; A cospan can be created by a pair of set functions with a common target set.
(deftype Cospan [a b c f g]
  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [a b c])))

(derive Cospan :locus.set.logic.structure.protocols/copresheaf)

; Cospan component sets and functions
(defn first-cospan-source
  [^Cospan cospan]

  (.-a cospan))

(defn second-cospan-source
  [^Cospan cospan]

  (.-b cospan))

(defn cospan-target
  [^Cospan cospan]

  (.-c cospan))

(defn first-cospan-function
  [cospan]

  (SetFunction. (.-a cospan) (.-c cospan) (.-f cospan)))

(defn second-cospan-function
  [cospan]

  (SetFunction. (.-b cospan) (.-c cospan) (.-g cospan)))

; Successor quivers for cospan copresheaves
(defmethod successor-quiver Cospan
  [cospan i]

  (cond
    (= i '()) (identity-function (cospan-target cospan))
    (= i '(0)) (first-cospan-function cospan)
    (= i '(1)) (second-cospan-function cospan)))

; Get the elements of a cospan copresheaf
(defmethod get-set Cospan
  [^Cospan cospan, i]

  (cond
    (= i '()) (cospan-target cospan)
    (= i '(0)) (first-cospan-source cospan)
    (= i '(1)) (second-cospan-source cospan)))

(defmethod get-function Cospan
  [^Cospan cospan, i]

  (cond
    (= i '(() ())) (identity-function (cospan-target cospan))
    (= i '((0) ())) (identity-function (first-cospan-source cospan))
    (= i '((1) ())) (identity-function (second-cospan-source cospan))
    (= i '((0) (0))) (first-cospan-function cospan)
    (= i '((1) (0))) (second-cospan-function cospan)))

; Create a cospan copresheaf from a pair of functions
(defn cospan
  [f g]

  (let [a (inputs f)
        b (inputs g)
        c (union (outputs f) (outputs g))]
    (Cospan. a b c f g)))

; Convert a relation into a cospan copresheaf
(defn relation-to-cospan
  [rel]

  (cospan
    (relation-transition-map rel 0 2)
    (relation-transition-map rel 1 2)))

; Generalized conversion routines
(defmulti to-cospan type)

(defmethod to-cospan Cospan
  [^Cospan cospan] cospan)

(defmethod to-cospan :locus.set.logic.core.set/universal
  [rel]

  (relation-to-cospan rel))

; The underlying relations of cospan copresheaves
(defmethod underlying-relation Cospan
  [^Cospan cospan]

  (let [f (first-cospan-function cospan)
        g (second-cospan-function cospan)]
    (apply
      union
      (map
        (fn [[a b]]
          (set
            (for [i (inputs f)
                  :when (= (f i) b)]
              (list i a b))))
        (underlying-relation g)))))

(defmethod underlying-multirelation Cospan
  [^Cospan cospan] (underlying-relation cospan))

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

(defn diset-image
  [cospan]

  (->Diset
    (first-cospan-image cospan)
    (second-cospan-image cospan)))

; Get the dual of a cospan copresheaf
(defn dual-cospan
  [^Cospan cospan]

  (cospan (.-g cospan) (.-f cospan)))

; Constructors for special types of cospans
(defn singleton-cospan
  [a b c]

  (cospan
    (mapfn {a c})
    (mapfn {b c})))

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

(defn constant-cospan
  [coll]

  (->Cospan coll coll coll identity identity))

(defn inclusion-cospan
  [a b c]

  (cospan
    (inclusion-function a c)
    (inclusion-function b c)))

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

; Convert cospans into functions
(defmethod to-function Cospan
  [^Cospan cospan]

  (->SetFunction
    (cartesian-coproduct (first-cospan-source cospan) (second-cospan-source cospan))
    (cospan-target cospan)
    (fn [[i v]]
      (case i
        0 (apply-first-cospan-function cospan v)
        1 (apply-second-cospan-function cospan v)))))

; Products and coproducts in the topos of cospan copresheaves
(defmethod product Cospan
  [& cospans]

  (Cospan.
    (apply product (map first-cospan-source cospans))
    (apply product (map second-cospan-source cospans))
    (apply product (map cospan-target cospans))
    (apply product (map first-cospan-function cospans))
    (apply product (map second-cospan-function cospans))))

(defmethod coproduct Cospan
  [& cospans]

  (Cospan.
    (apply coproduct (map first-cospan-source cospans))
    (apply coproduct (map second-cospan-source cospans))
    (apply coproduct (map cospan-target cospans))
    (apply coproduct (map first-cospan-function cospans))
    (apply coproduct (map second-cospan-function cospans))))

; Subobjects of the topos of cospans
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

; Ontology of subobjects in the topos of cospan copresheaves
(defn subcospan?
  [cospan new-first-source new-second-source new-target]

  (let [fn1 (first-cospan-function cospan)
        fn2 (second-cospan-function cospan)]
    (and
      (superset? (list (set-image fn1 new-first-source) new-target))
      (superset? (list (set-image fn2 new-second-source) new-target)))))

(defn subcospan-closure
  [cospan new-first-source new-second-source new-target]

  (list
    new-first-source
    new-second-source
    (union
      new-target
      (set-image (first-cospan-function cospan) new-first-source)
      (set-image (second-cospan-function cospan) new-second-source))))

; Enumeration theory for cospan copresheaves
(defn subcospans
  [cospan]

  (set
    (mapcat
      (fn [[first-source second-source]]
        (let [minimal-target-set (union
                                   (set-image (first-cospan-function cospan) first-source)
                                   (set-image (second-cospan-function cospan) second-source))
              possible-target-additions (difference
                                          (cospan-target cospan)
                                          minimal-target-set)]
          (map
            (fn [new-targets]
              (list
                first-source
                second-source
                (union new-targets minimal-target-set)))
            (power-set possible-target-additions))))
      (cartesian-product
        (power-set (first-cospan-source cospan))
        (power-set (second-cospan-source cospan))))))

; Relations between subcopsans
(defn covering-subcospans
  [cospan first-source second-source target]

  (let [f1 (first-cospan-function cospan)
        f2 (second-cospan-function cospan)]
    (set
      (concat
        (let [first-additions (set
                                (filter
                                  (fn [i]
                                    (contains? target (f1 i)))
                                  (difference (first-cospan-source cospan) first-source)))]
          (map
            (fn [first-addition]
              (list (conj first-source first-addition) second-source target))
            first-additions))
        (let [second-additions (set
                                 (filter
                                   (fn [i]
                                     (contains? target (f2 i)))
                                   (difference (second-cospan-source cospan) second-source)))]
          (map
            (fn [second-addition]
              (list first-source (conj second-source second-addition) target))
            second-additions))
        (let [target-additions (difference (cospan-target cospan) target)]
          (map
            (fn [target-addition]
              (list first-source second-source (conj target target-addition)))
            target-additions))))))

(defn subcospans-covering
  [cospan]

  (set
    (mapcat
      (fn [[a b c]]
        (map
          (fn [[x y z]]
            (list (list a b c) (list x y z)))
          (covering-subcospans cospan a b c)))
      (subcospans cospan))))

; Cospan quotients
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

; Quotients in the topos of cospan copresheaves
(defn cospan-congruence?
  [cospan first-source-partition second-source-partition target-partition]

  (let [fn1 (first-cospan-function cospan)
        fn2 (second-cospan-function cospan)]
    (and
      (io-relation? fn1 first-source-partition target-partition)
      (io-relation? fn2 second-source-partition target-partition))))

(defn cospan-congruence-closure
  [cospan first-source-partition second-source-partition target-partition]

  (list
    first-source-partition
    second-source-partition
    (join-set-partitions
      target-partition
      (partition-image (first-cospan-function cospan) first-source-partition)
      (partition-image (second-cospan-function cospan) second-source-partition))))

; Congruences in the topos of cospans
(defn cospan-congruences
  [cospan]

  (set
    (mapcat
      (fn [[first-partition second-partition]]
        (let [minimal-target-partition (join-set-partitions
                                         (partition-image (first-cospan-function cospan) first-partition)
                                         (partition-image (second-cospan-function cospan) second-partition))]
          (map
            (fn [new-target-partition]
              (list first-partition second-partition new-target-partition))
            (set-partition-coarsifications minimal-target-partition))))
      (cartesian-product
        (set-partitions (first-cospan-source cospan))
        (set-partitions (second-cospan-source cospan))))))

; Covering relation in the lattice of congruences of a cospan copresheaf
(defn cospan-covering-congruences
  [cospan first-source-partition second-source-partition target-partition]

  (let [f1 (first-cospan-function cospan)
        f2 (second-cospan-function cospan)]
    (set
      (concat
        (for [i (direct-set-partition-coarsifications first-source-partition)
              :when (set-superpartition? (list (partition-image f1 i) target-partition))]
          (list i second-source-partition target-partition))
        (for [i (direct-set-partition-coarsifications second-source-partition)
              :when (set-superpartition? (list (partition-image f2 i) target-partition))]
          (list first-source-partition i target-partition))
        (for [i (direct-set-partition-coarsifications target-partition)]
          (list first-source-partition second-source-partition i))))))

(defn cospan-congruences-covering
  [cospan]

  (set
    (mapcat
      (fn [[p q r]]
        (map
          (fn [[new-p new-q new-r]]
            (list [p q r] [new-p new-q new-r]))
          (cospan-covering-congruences cospan p q r)))
      (cospan-congruences cospan))))

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

; Visualisation routines for cospan copresheaves
(defmethod visualize Cospan
  [^Cospan cospan]

  (let [[p v] (generate-copresheaf-data
                {0 (first-cospan-source cospan)
                 1 (second-cospan-source cospan)
                 2 (cospan-target cospan)}
                #{(list 0 2 (first-cospan-function cospan))
                  (list 1 2 (second-cospan-function cospan))})]
    (visualize-clustered-digraph* "BT" p v)))
