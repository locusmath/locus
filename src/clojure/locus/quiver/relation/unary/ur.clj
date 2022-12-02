(ns locus.quiver.relation.unary.ur
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.quiver.relation.binary.product :refer :all]))

; Unary relations are sets of ordered singletons
; As a consequence they are essentially isomorphic to ordinary sets.

; A data type for unary relations
(deftype UnaryRelation [coll]
  clojure.lang.Seqable
  (seq [this]
    (map
      (fn [i]
        (list i))
      coll))

  clojure.lang.Counted
  (count [this]
    (count coll))

  Object
  (toString [this]
    (str coll "¹"))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (singular-seq? arg)
      (let [val (first arg)]
        (coll val))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive UnaryRelation :locus.base.logic.core.set/universal)

(defmethod print-method UnaryRelation [^UnaryRelation v ^java.io.Writer w]
  (.write w (.toString v)))

(defmethod vertices UnaryRelation
  [^UnaryRelation rel]

  (.coll rel))

; Unary multirelations
(defn unary-relation
  [pred]

  (if (seqable-universal? pred)
    (set
      (map
        (fn [i]
          (list i))
        pred))
    (fn [coll]
      (and
        (seq? coll)
        (= (count coll) 1)
        (every? pred coll)))))

(defn unary-multirelation
  [coll]

  (multiset (map (fn [i] (list i)) coll)))

; Unary multirelations
(defn unary-multirelation?
  [rel]

  (and
    (multiset? rel)
    (every? singular-seq? rel)))

(def size-two-unary-multirelation?
  (intersection
    size-two-multiset?
    unary-multirelation?))

(def size-three-unary-multirelation?
  (intersection
    size-three-multiset?
    unary-multirelation?))

(def size-four-unary-multirelation?
  (intersection
    size-four-multiset?
    unary-multirelation?))

; Unary relations
(def unary-relation?
  (power-set singular-seq?))

(def unique-unary-relation?
  (intersection
    unary-relation?
    (fn [coll] (<= (count coll) 1))))

(def size-two-unary-relation?
  (intersection
    unary-relation?
    size-two-universal?))

(def size-three-unary-relation?
  (intersection
    unary-relation?
    size-three-universal?))

(def size-four-unary-relation?
  (intersection
    unary-relation?
    size-four-universal?))