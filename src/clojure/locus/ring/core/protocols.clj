(ns locus.ring.core.protocols
  (:refer-clojure :exclude [/ + - *])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]))

; This file contains generic multimethods that are applicable to rings, semirings,
; quotient rings, or any other type of arithmetic structure in this system.

; Rings and semirings are combinations of semigroups
(defmulti additive-semigroup type)

(defmulti multiplicative-semigroup type)

; Make ring is the general method we use for creating rings
(defmulti make-ring (fn [a b] (type a)))

; Both rings and semirings have multiplicative duals
(defn opposite-ring
  [semiring]

  (make-ring
    (additive-semigroup semiring)
    (dual (multiplicative-semigroup semiring))))

; Rings and semirings are algebras that are defined
; by collections of set functions.
(def addition-function
  (comp underlying-function additive-semigroup))

(def additive-identity-function
  (comp identity-element-function additive-semigroup))

(def additive-inverse-function
  (comp inverse-function additive-semigroup))

(def multiplication-function
  (comp underlying-function multiplicative-semigroup))

(def multiplicative-identity-function
  (comp identity-element-function multiplicative-semigroup))

; Ontology of rings and semirings
(derive ::semiring :locus.elementary.function.core.protocols/structured-set)
(derive ::ring ::semiring)

; Predicates for rings and semirings
(defmulti semiring? type)

(defmethod semiring? :default
  [x] (isa? (type x) ::semiring))

(defmulti ring? type)

(defmethod ring? :default
  [x] (isa? (type x) ::ring))

(defn intrinsic-ring?
  [x] (isa? (type x) ::ring))

; This is just a useful utility function for displaying the tables of finite
; rings and finite semirings.
(defn display-tables
  [ring]

  (do
    (println "+")
    (display-table (additive-semigroup ring))
    (println "")
    (println "*")
    (display-table (multiplicative-semigroup ring))))

