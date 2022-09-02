(ns locus.elementary.topoi.nset.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
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

(defn nth-set
  [^NSet nset, n]

  (nth (.colls nset) n))

(defn nset-type
  [^NSet coll]

  (count (.colls coll)))

; Get the nset of an object
(defn nset
  [obj]

  (when (or (vector? obj) (seq? obj))
    (NSet. obj)))

; Convert a
(defmulti to-nset type)

(defmethod to-nset Diset
  [coll]

  (NSet. [(first-set coll) (second-set coll)]))

(defmethod to-nset :default
  [coll]

  (when (universal? coll)
    (NSet. [coll])))

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

(defmethod sub NSet
  [nset]

  (->Lattice
    (nset-subalgebras nset)
    join-set-sequences
    meet-set-sequences))

(defmethod con NSet
  [nset]

  (->Lattice
    (nset-congruences nset)
    join-set-sequence-congruences
    meet-set-sequence-congruences))

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

