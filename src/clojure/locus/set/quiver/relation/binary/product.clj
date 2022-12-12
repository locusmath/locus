(ns locus.set.quiver.relation.binary.product
  (:require [clojure.set]
            [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all])
  (:import [locus.set.logic.core.set Universal SeqableUniversal]))

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

(derive BinaryCartesianProduct :locus.set.logic.limit.product/cartesian-product)

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

; We will also create a special data type for dealing with complete
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

(derive CompleteRelation :locus.set.logic.limit.product/cartesian-product)

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

; Special mechanisms of getting vertices
(defmethod vertices CompleteRelation
  [rel]

  (.coll rel))

(defmethod vertices BinaryCartesianProduct
  [rel]

  (union (relation-domain rel)
         (relation-codomain rel)))