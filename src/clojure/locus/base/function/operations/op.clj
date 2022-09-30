(ns locus.base.function.operations.op
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.unary.ur :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.ternary.op :refer :all]
            [locus.elementary.relation.ternary.tr :refer :all]
            [locus.elementary.relation.quaternary.qr :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; Ontology of operations
(defn operation?
  [func]

  (and
    (set-function? func)
    (relation? (inputs func))))

(defn nary-operation?
  [func]

  (and
    (set-function? func)
    (nary-relation? (inputs func))))

(defn unary-operation?
  [func]

  (and
    (set-function? func)
    (unary-relation? (inputs func))))

(defn binary-operation?
  [func]

  (and
    (set-function? func)
    (binary-relation? (inputs func))))

(defn ternary-operation?
  [func]

  (and
    (set-function? func)
    (ternary-relation? (inputs func))))

(defn quaternary-operation?
  [func]

  (and
    (set-function? func)
    (quaternary-relation? (inputs func))))

; Table functions
(defn table-function?
  [func]

  (cartesian-product? (inputs func)))

(defn square-table-function?
  [func]

  (complete-relation? (inputs func)))

; Magma functions
(defn magma-function
  [coll func]

  (SetFunction.
    (complete-relation coll)
    coll
    func))

(defn magma-function?
  [func]

  (and
    (square-table-function? func)
    (equal-universals?
      (vertices (inputs func))
      (outputs func))))

(defn commutative-magma-function?
  [func]

  (and
    (magma-function? func)
    (every?
      (fn [pair]
        (= (func pair)
           (func (reverse pair))))
      (inputs func))))

(defn half-existent-triple?
  "Check if a(bc) exists but not (ab)c or vice versa."
  [func triple]

  (let [dom (inputs func)
        front-first-exists? (and
                              (dom (butlast triple))
                              (dom (list (func (butlast triple)) (last triple))))
        back-first-exists? (and
                             (dom (rest triple))
                             (dom (list (first triple) (func (rest triple)))))]
    (or
      (and front-first-exists? (not back-first-exists?))
      (and back-first-exists? (not front-first-exists?)))))

(defn existent-triple?
  "Check if a triple of terms exists wit respect to a binary operation"
  [func triple]

  (let [dom (inputs func)]
    (and
      (dom (butlast triple))
      (dom (rest triple))
      (dom (list (first triple) (func (rest triple))))
      (dom (list (func (butlast triple)) (last triple))))))

(defn associative-operation?
  [func]

  (and
    (binary-operation? func)
    (every?
      (fn [triple]
        (or (not (existent-triple? func triple))
            (= (func (list (first triple) (func (rest triple))))
               (func (list (func (butlast triple)) (last triple))))))
      (cartesian-power (vertices (inputs func)) 3))))

(def semigroup-function?
  (intersection
    associative-operation?
    magma-function?))

(def commutative-semigroup-function?
  (intersection
    associative-operation?
    commutative-magma-function?))

(defn partial-semigroup-function?
  [func]

  (and
    (associative-operation? func)
    (every?
      (fn [triple]
        (not (half-existent-triple? func triple)))
      (cartesian-power (vertices (inputs func)) 3))))

; Test for an identity element
(defn identity-input-element?
  [func id]

  (every?
    (fn [elem]
      (and
        (= (func (list id elem)) elem)
        (= (func (list elem id)) elem)))
    (outputs func)))

(defn identity-input-elements
  [func]

  (filter
    (fn [i]
      (identity-input-element? func i))
    (outputs func)))

(defn monoid-function?
  [func]

  (and
    (semigroup-function? func)
    (not (empty? (identity-input-elements func)))))

(defn unital-magma-function?
  [func]

  (and
    (semigroup-function? func)
    (not (empty? (identity-input-elements func)))))

(def commutative-monoid-function?
  (intersection
    monoid-function?
    commutative-magma-function?))

; Get the partition of the domain of a binary operation by commutativity
(defn commutativity-domain-partition
  [func]

  (let [coll (inputs func)]
    (pn
      (fn [a b]
        (= (set a) (set b)))
      coll)))

(defn commutativity-codomain-partition
  [func]

  (partition-image func (commutativity-domain-partition func)))

(defn commutativity-quotient-function
  [func]

  (quotient-function
    func
    (commutativity-domain-partition func)
    (commutativity-codomain-partition func)))

