(ns locus.nonassociative.magma.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer  :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (clojure.lang IPersistentMap)))

; Let S be a set then a magma on S is simply a function of the form
; f : S^2 -> S. We consider magmas to be a special subcategory of the
; topos functions of this form. Each magma subobject produces a subfunction
; and each magma congruence produces a congruence of functions in the topos
; Sets^(->) of functions.
(deftype Magma [coll op]
  ConcreteObject
  (underlying-set [this] coll)

  StructuredDiset
  (first-set [this] coll)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver coll 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation coll))
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Magma :locus.set.copresheaf.structure.core.protocols/magma)

; Convert certain objects into magmas
(defmulti to-magma type)

(defmethod to-magma :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (Magma. (underlying-set semigroup) (fn [pair] (semigroup pair))))

(defmethod to-magma SetFunction
  [func]

  (Magma. (outputs func) func))

(defmethod to-magma IPersistentMap
  [coll]

  (to-magma (mapfn coll)))

; Create a magma by a table
(defn magma-by-table
  [coll]

  (let [n (count coll)]
    (Magma.
      (->RangeSet 0 n)
      (fn [[i j]]
        (nth (nth coll i) j)))))

; Special elements of magmas
(defn idempotents-of-magma
  [magma]

  (filter
    (fn [i]
      (= i (magma (list i i))))
    (underlying-set magma)))

; Get the central elements of a magma
(defn central-magma-element?
  [magma elem]

  (every?
    (fn [i]
      (= (magma (list elem i))
         (magma (list i elem))))
    (morphisms magma)))

(defn central-elements-of-magma
  [magma]

  (set
    (filter
      (fn [morphism]
        (central-magma-element? magma morphism))
      (morphisms magma))))

(defn magma-element-centralizer
  [magma elem]

  (set
    (filter
      (fn [morphism]
        (= (magma (list morphism elem))
           (magma (list elem morphism))))
      (morphisms magma))))

; We can dualize any magma by reversing its ordering
(defmethod dual Magma
  [magma]

  (Magma.
    (underlying-set magma)
    (fn [pair] (magma (reverse pair)))))

(defmethod product Magma
  [& magmas]

  (Magma.
    (apply cartesian-product (map underlying-set magmas))
    (fn [[coll1 coll2]]
      (map
        (fn [i]
          ((nth magmas i) (list (nth coll1 i) (nth coll2 i))))
        (range (count magmas))))))

; Get if a given subset is a submagma
(defn submagma?
  [magma coll]

  (every?
    (fn [pair]
      (contains? coll (magma pair)))
    (cartesian-power coll 2)))

(defn enumerate-submagmas
  [magma]

  (set
    (filter
      (fn [coll]
        (submagma? magma coll))
      (power-set (underlying-set magma)))))

(defn submagma
  [magma coll]

  (Magma. coll (.op magma)))

; Test if a given partition constitutes a congruence of the magma
(defn magma-congruence?
  [magma partition]

  (every?
    (fn [[coll1 coll2]]
      (equal-seq?
        (map
          (comp (partial projection partition) magma)
          (cartesian-product coll1 coll2))))
    (cartesian-power partition 2)))

(defn enumerate-magma-congruences
  [magma]

  (set
    (filter
      (fn [partition]
        (magma-congruence? magma partition))
      (set-partitions (set (underlying-set magma))))))

(defn quotient-magma
  [magma partition]

  (Magma.
    partition
    (fn [[c1 c2]]
      (projection partition (magma (list (first c1) (first c2)))))))

; Magmas as special types of magmoids with a single element
(defmulti magma? type)

(defmethod magma? :locus.set.copresheaf.structure.core.protocols/magma
  [magma] true)

(defmethod magma? :locus.set.copresheaf.structure.core.protocols/magmoid
  [magmoid] (= (count (objects magmoid)) 1))

; Unital magmas include monoids as a special case
(defmulti unital-magma? type)

(defmethod unital-magma? :locus.set.copresheaf.structure.core.protocols/monoid
  [monoid] true)

(defmethod unital-magma? :default
  [magma]

  (letfn [(magma-identity-element? [magma identity-element]
            (every?
              (fn [i]
                (= (magma (list identity-element i))
                   (magma (list i identity-element))
                   i))
              (morphisms magma)))]
    (not
      (every?
        (fn [i]
          (not (magma-identity-element? magma i)))
        (morphisms magma)))))

; Ontology of magmas
(defn magma-with-zero?
  [magma]

  (letfn [(magma-zero-element? [magma zero-element]
            (every?
              (fn [i]
                (= (magma (list i zero-element))
                   (magma (list zero-element i))
                   zero-element))
              (morphisms magma)))]
    (not
      (every?
        (fn [i]
          (not (magma-zero-element? magma i)))
        (morphisms magma)))))

(defn commutative-magma?
  [magma]

  (and
    (magma? magma)
    (every?
      (fn [pair]
        (= (magma pair) (magma (reverse pair))))
      (inputs magma))))

(defn anticommutative-magma?
  [magma]

  (and
    (magma? magma)
    (every?
      (fn [pair]
        (or
          (let [[a b] pair]
            (= a b))
          (not= (magma pair) (magma (reverse pair)))))
      (inputs magma))))

(defn unipotent-magma?
  [magma]

  (and
    (magma? magma)
    (equal-seq?
      (map
        (fn [morphism]
          (magma (list morphism morphism)))
        (morphisms magma)))))

(defn idempotent-magma?
  [magma]

  (and
    (magma? magma)
    (every?
      (fn [i]
        (= (magma (list i i)) i))
      (underlying-set magma))))

(def idempotent-commutative-magma?
  (intersection
    commutative-magma?
    idempotent-magma?))

