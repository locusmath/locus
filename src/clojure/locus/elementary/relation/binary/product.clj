(ns locus.elementary.relation.binary.product
  (:require [clojure.set]
            [locus.elementary.logic.base.core :refer :all])
  (:import [locus.elementary.logic.base.core Universal SeqableUniversal]))

; Let Sets be the topos of sets. Recall that every topos is associated with products and coproducts.
; This file handles the formation of these products and coproducts of sets.

; Cartesian products
(defn enumerate-cartesian-product
  [& colls]

  (letfn [(place-system [coll]            
            (fn [j]
              (map
               (fn [i]
                 (mod (quot j (apply * (take i coll)))
                      (nth coll i)))
               (range (count coll)))))]
    (let [sorted-colls (map (comp vec seq) colls)
          coll-counts (map count colls)
          func (place-system coll-counts)]
      (map
       (fn [i]
         (let [current-coordinate (func i)]
           (map-indexed
            (fn [first-index second-index]
              (nth (nth sorted-colls first-index) second-index))
            current-coordinate)))
       (range (apply * coll-counts))))))

(defn seqable-cartesian-product
  [& colls]

  (SeqableUniversal.
   (intersection
    seq?
    (fn [coll]
      (and
       (= (count coll) (count colls))
       (every?
        (fn [i]
          ((nth colls i) (nth coll i)))
        (range (count colls))))))
   (apply enumerate-cartesian-product colls)
   {:count (apply * (map count colls))}))

(defn cartesian-product-classifier
  [& colls]

  (fn [coll]
    (and
      (seq? coll)
      (= (count coll) (count colls))
      (every?
        (fn [i]
          ((nth colls i) (nth coll i)))
        (range (count colls))))))

(defn cartesian-product
  [& colls]

  (if (every? seqable-universal? colls)
    (set (apply enumerate-cartesian-product colls))
    (apply cartesian-product-classifier colls)))

(defn enumerate-cartesian-power
  [coll n]

  (apply enumerate-cartesian-product (repeat n coll)))

(defn seqable-cartesian-power
  [coll n]

  (apply seqable-cartesian-product (repeat n coll)))

(defn cartesian-power
  [coll n]

  (apply cartesian-product (repeat n coll)))

; The category theoretic dual operation to the cartesian product is the
; coproduct of sets, which we can define here by turning a coproduct of
; sets into a numerically indexed relation.
(defn cartesian-coproduct
  [& colls]
  
  (apply
   union
   (map-indexed
    (fn [i v]
      (set
       (map
        (fn [j]
          (list i j))
        v)))
    colls)))

(defn cartesian-coproduct-classifier
  [& colls]

  (let [n (count colls)]
    (fn [[i x]]
     (and
       (natural-number? i)
       (< i n)
       ((nth colls i) x)
       true))))

; Domain and codomain
; The two main properties of a function are the set partition
; of the domain and the multiset of elements of the codomain.
(defmulti relation-domain
  (fn [a] (type a)))

(defmulti relation-codomain
  (fn [b] (type b)))

(defmethod relation-domain :default
  [rel]

  (set (map first rel)))

(defmethod relation-codomain :default
  [rel]

  (set (map second rel)))

; Intrinsic domains and codomains of relation classes
(defprotocol EmbeddedRelation
  "An embedded relation is simply a relation R <= A x B. So that the relation R is inherently embedded
  within the cartesian product of two sets. This protocol defines methods for accessing these two sets
  of an embedded relation."

  (intrinsic-domain [this]
    "Access the embedding domain of an embedded relation.")
  (intrinsic-codomain [this]
    "Access the embedding codomain of an embedded relation."))

; Binary cartesian product
(deftype BinaryCartesianProduct [domain codomain]
  EmbeddedRelation
  (intrinsic-domain [this] domain)
  (intrinsic-codomain [this] codomain)

  clojure.lang.Seqable
  (seq [this]
    (enumerate-cartesian-product (set domain) (set codomain)))
  
  clojure.lang.Counted
  (count [this]
    (* (count domain) (count codomain)))

  Object
  (toString [this]
    (str domain " × " codomain))
  
  clojure.lang.IFn
  (invoke [this obj]
    (and
     (seq? obj)
     (= (count obj) 2)
     (and
      (if (set? domain)
        (contains? domain (first obj))
        (domain (first obj)))
      (if (set? codomain)
        (contains? codomain (second obj))
        (codomain (second obj))))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defmethod print-method BinaryCartesianProduct [v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod relation-domain BinaryCartesianProduct
  [r] (intrinsic-domain r))

(defmethod relation-codomain BinaryCartesianProduct
  [r] (intrinsic-codomain r))

(defmethod intersection* #{BinaryCartesianProduct}
  [a b]

  (BinaryCartesianProduct.
   (intersection (relation-domain a) (relation-domain b))
   (intersection (relation-codomain a) (relation-codomain b))))

(defmethod seqable-universal? BinaryCartesianProduct
  [a] true)

; We will also create a special daat type for dealing with complete 
; relations in particular.
(deftype CompleteRelation [coll]
  EmbeddedRelation
  (intrinsic-domain [this] coll)
  (intrinsic-codomain [this] coll)

  clojure.lang.Seqable
  (seq [this]
    (enumerate-cartesian-product coll coll))
  
  clojure.lang.Counted
  (count [this]
    (* (count coll) (count coll)))

  Object
  (toString [this]
    (str coll "²"))
  
  clojure.lang.IFn
  (invoke [this obj]
    (and
     (seq? obj)
     (= (count obj) 2)
     (if (set? coll)
       (and (contains? coll (first obj))
            (contains? coll (second obj)))
       (and (coll (first obj))
            (coll (second obj))))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defmethod print-method CompleteRelation [v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod relation-domain CompleteRelation
  [r] (intrinsic-domain r))

(defmethod relation-codomain CompleteRelation
  [r] (intrinsic-codomain r))

(defmethod intersection* #{CompleteRelation}
  [a b]

  (CompleteRelation.
   (intersection (relation-domain a) (relation-domain b))))

(defmethod seqable-universal? CompleteRelation
  [a] true)

; Vertices are a multimethod now applicable to any number 
; of relational predicate data types.
(defmulti vertices
  (fn [a] (type a)))

(defmethod vertices CompleteRelation
  [rel]

  (.coll rel))

(defmethod vertices BinaryCartesianProduct
  [rel]

  (union (relation-domain rel)
         (relation-codomain rel)))

(defmethod vertices :default
  [rel]

  (apply
   union
   (for [i rel
         :when (seq? i)]
     (set i))))
