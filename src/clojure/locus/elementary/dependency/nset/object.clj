(ns locus.elementary.dependency.nset.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diset.core.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)))

; Let Sets^n be the topos of copresheaves over a discrete category. Then then the objects of the
; topos Sets^n are called nsets and they are defined now by the NSet class. An nset is a natural
; generalization of the concept of a set pair in the topos Sets^2 to an arbitrary number of sets.
; This generalized class allows to us to handle all kinds of copresheaves over discrete categories.
; An NSet is defined by the data of an array of sets. All topos theoretic operations, like
; products and coproducts are defined on them accordingly.

(deftype NSet [colls]
  Object
  (toString [this]
    (str "(" (apply str (interpose " " colls)) ")")))

(defmethod print-method NSet [^NSet v ^java.io.Writer w]
  (.write w (.toString v)))

; Components of nsets
(defn nth-set
  [^NSet nset, n]

  (nth (.colls nset) n))

(defmethod get-set NSet
  [^NSet nset, n]

  (nth-set nset n))

(defmethod get-function NSet
  [^NSet nset, [a b]]

  (identity-function (nth-set nset a)))

; Get the parent topos of a nset
(defn nset-type
  [^NSet coll]

  (count (.colls coll)))

; Get the nset of an object
(defn nset
  [obj]

  (when (or (vector? obj) (seq? obj))
    (NSet. obj)))

; Convert an object into a copresheaf over a discrete category
(defmulti to-nset type)

(defmethod to-nset Diset
  [coll]

  (NSet. [(first-set coll) (second-set coll)]))

(defmethod to-nset :locus.base.logic.core.set/universal
  [coll]

  (NSet. [coll]))

; A discrete copresheaf whose sets are all singletons
(defn singleton-nset
  [& elems]

  (->NSet
    (map
      (fn [i]
        #{i})
      elems)))

; Products and coproducts in the topos of copresheaves over a discrete category
(defmethod product NSet
  [& args]

  (NSet.
    (let [n (nset-type (first args))]
      (map
        (fn [i]
          (apply
            cartesian-product
            (map
              (fn [arg]
                (nth-set arg i))
              args)))
        (range n)))))

(defmethod coproduct NSet
  [& args]

  (NSet.
    (let [n (nset-type (first args))]
      (map
        (fn [i]
          (apply
            cartesian-coproduct
            (map
              (fn [arg]
                (nth-set arg i))
              args)))
        (range n)))))

; Subalgebra and congruence lattices of copresheaves of discrete categories
(defn join-set-sequences
  [& args]

  (apply (partial map union) args))

(defn meet-set-sequences
  [& args]

  (apply (partial map intersection) args))

(defn join-set-sequence-congruences
  [& args]

  (apply (partial map join-set-partitions) args))

(defn meet-set-sequence-congruences
  [& args]

  (apply (partial map meet-set-partitions) args))

; Subobjects and quotients of nsets
(defn nset-subalgebras
  [nset]

  (apply
    cartesian-product
    (map
      power-set
      (.colls nset))))

(defn nset-congruences
  [nset]

  (apply
    cartesian-product
    (map
      set-partitions
      (.colls nset))))

; Ontology of sequences of sets
(defn nset?
  [coll]

  (= (type coll) NSet))

(defn equal-nset?
  [nset]

  (and
    (nset? nset)
    (let [coll (.colls ^NSet nset)]
      (or
        (empty? coll)
        (apply = coll)))))

; Visualisation of nsets
(defmethod visualize NSet
  [nset]

  (let [[p r] (generate-copresheaf-data (vector->map (vec (.colls nset))) #{})]
    (visualize-clustered-digraph* "BT" p r)))