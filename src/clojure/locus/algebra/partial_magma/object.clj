(ns locus.algebra.partial-magma.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; A partial magma is a function f : R -> S defined on a binary relation R
; which is a subset of S^2. So that it is defined on a subset of the possible
; values that an ordinary magma might be defined on. The relation of the
; domain is an extra piece of data needed to define the partial magma.
(deftype PartialMagma [rel coll op]
  ConcreteObject
  (underlying-set [this] coll)

  ConcreteMorphism
  (inputs [this] rel)
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PartialMagma :locus.base.logic.structure.protocols/structured-set)

; Conversion routines for partial magmas
(defmulti to-partial-magma type)

(defmethod to-partial-magma PartialMagma
  [magma] magma)

(defmethod to-partial-magma SetFunction
  [func]

  (PartialMagma.
    (inputs func)
    (union (vertices (inputs func)) (outputs func))
    (.func func)))

; Get the partial magma of a category
(defn categorical-composition-operation
  [category]

  (->PartialMagma
    (inputs category)
    (morphisms category)
    (fn [pair] (category pair))))

; Duality of partial magmas
(defmethod dual PartialMagma
  [partial-magma]

  (PartialMagma.
    (transpose (.rel partial-magma))
    (underlying-set partial-magma)
    (fn [pair] (partial-magma (reverse pair)))))

(defmethod product PartialMagma
  [& magmas]

  (PartialMagma.
    (apply cartesian-product (map inputs magmas))
    (apply cartesian-product (map outputs magmas))
    (fn [[coll1 coll2]]
      (map
        (fn [i]
          ((nth magmas i) (list (nth coll1 i) (nth coll2 i))))
        (range (count magmas))))))

; Subalgebra lattices of partial magmas
(defn partial-submagma?
  [magma coll]

  (every?
    (fn [pair]
      (contains? coll (magma pair)))
    (subrelation (inputs magma) coll)))

(defmethod sub PartialMagma
  [magma ]

  (->Lattice
    (set
      (filter
        (fn [coll]
          (partial-submagma? magma coll))
        (power-set (underlying-set magma))))
    union
    intersection))

; Utilize a projection functions in order to improve performance
(defn partial-magma-congruence?
  [magma partition]

  (letfn [(value-singular-map? [coll]
            (every?
              (fn [i]
                (= (count i) 1))
              (vals coll)))]
    (let [func (partition->projection partition)]
      (value-singular-map?
        (loop [keys #{}
              rval {}
              current-domain (seq (inputs magma))]
         (if (empty? current-domain)
           rval
           (let [current-element (first current-domain)
                 current-element-type (map func current-element)
                 old-element? (contains? keys current-element-type)
                 output-element (magma current-element)
                 output-type (func output-element)]
             (recur
               (if old-element?
                 keys
                 (conj keys current-element-type))
               (assoc
                 rval
                 current-element-type
                 (if old-element?
                   (conj (get rval current-element-type) output-type)
                   #{output-type}))
               (rest current-domain)))))))))

(defmethod con PartialMagma
  [partial-magma]

  (->Lattice
    (set
      (filter
        (fn [partition]
          (partial-magma-congruence? partial-magma partition))
        (set-partitions (underlying-set partial-magma))))
    join-set-partitions
    meet-set-partitions))





