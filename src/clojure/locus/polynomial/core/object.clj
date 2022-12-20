(ns locus.polynomial.core.object
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.module.vector.rset :refer :all])
  (:import (locus.algebra.group.core.object Group)
           (locus.algebra.semigroup.monoid.object Monoid)
           (locus.algebra.semigroup.core.object Semigroup)))

; Polynomials are the most basic units of abstract algebra
; They should be represented as maps of multisets
(deftype Polynomial [semiring data]
  RingedSet
  (ring-of-coefficients [this] semiring)
  (terms [this] (set (keys data)))
  (coefficient [this arg]
    (let [v (get data arg)]
      (if (nil? v)
        (identity-element (additive-semigroup semiring))
        v)))

  Object
  (toString [this] (str "#R" (.toString data))))

(defmethod print-method Polynomial [^Polynomial v, ^java.io.Writer w]
  (.write w (.toString v)))

; Arithmetic operations in polynomial rings
(defn monomials
  [polynomial]

  (let [ring (ring-of-coefficients polynomial)]
    (map
      (fn [[i v]]
        (Polynomial.
          ring
          {i v}))
      (.data polynomial))))

(defn map-polynomial-coefficients
  [func polynomial]

  (Polynomial.
    (ring-of-coefficients polynomial)
    (into
      {}
      (for [i (terms polynomial)]
        [i (func (coefficient polynomial i))]))))

(defmethod negate Polynomial
  [polynomial]

  (let [ring (ring-of-coefficients polynomial)
        negation-function (additive-inverse-function ring)]
    (map-polynomial-coefficients negation-function polynomial)))

(defmethod add [Polynomial Polynomial]
  [polynomial1 polynomial2]

  (let [ring (ring-of-coefficients polynomial1)
        add (additive-semigroup ring)
        additive-identity (first (identity-elements add))]
    (Polynomial.
      ring
      (into
        {}
        (for [i (union (terms polynomial1) (terms polynomial2))
              :let [sum (add (list (coefficient polynomial1 i)
                                   (coefficient polynomial2 i)))]
              :when (not= additive-identity sum)]
          [i sum])))))

(defmethod multiply [Polynomial Polynomial]
  [polynomial1 polynomial2]

  (let [ring (ring-of-coefficients polynomial1)
        mul (multiplicative-semigroup ring)]
    (let [monomial-products (map
                              (fn [[monomial1 monomial2]]
                                (let [data1 (.data monomial1)
                                      data2 (.data monomial2)
                                      [i1 v1] (first (seq data1))
                                      [i2 v2] (first (seq data2))]
                                  (Polynomial.
                                    ring
                                    {(locus.set.logic.core.set/add i1 i2) (mul (list v1 v2))})))
                              (cartesian-product
                                (set (monomials polynomial1))
                                (set (monomials polynomial2))))]
      (if (empty? monomial-products)
        (Polynomial. ring {})
        (apply + monomial-products)))))

; Polynomials
(defn zero-polynomial
  [ring]

  (Polynomial. ring {}))

(defn one-polynomial
  [ring]

  (let [one (first (identity-elements (multiplicative-semigroup ring)))]
    (Polynomial.
      ring
      {(multiset '()) one})))

(defn polynomial-ring
  [ring]

  (let [classifier (fn [polynomial]
                     (and
                       (= (type polynomial) Polynomial)
                       (= (.semiring polynomial) ring)))]
    (make-ring
      (if (intrinsic-group? (additive-semigroup ring))
        (Group.
          classifier
          (fn [[a b]]
            (+ a b))
          (zero-polynomial ring)
          (fn [a]
            (- a)))
        (Monoid.
          classifier
          (fn [[a b]]
            (+ a b))
          (zero-polynomial ring)))
      (if (intrinsic-monoid? (multiplicative-semigroup ring))
        (Monoid.
          classifier
          (fn [[a b]]
            (* a b))
          (one-polynomial ring))
        (Semigroup.
         classifier
         (fn [[a b]]
           (* a b)))))))

(defmethod get-semiring Polynomial
  [^Polynomial polynomial]

  (polynomial-ring (.semiring polynomial)))

; Generic conversion routines
(defmulti to-polynomial type)

(defmethod to-polynomial Polynomial
  [polynomial] polynomial)

; Constructors for polynomials
(defn univariate-polynomial
  [ring coll]

  (Polynomial.
    qq
    (into
      {}
      (for [i (range (count coll))
            :let [coefficient (nth coll i)]
            :when (not (zero? coefficient))]
        [(repeat-multiset i 0) coefficient]))))

(defn integer-univariate-polynomial
  [coll]

  (univariate-polynomial zz coll))

(defn constant-polynomial
  [ring n]

  (Polynomial. ring {(multiset '()) n}))

(def circle-polynomial
  (Polynomial.
    qq
    {(multiset '(0 0)) 1
     (multiset '(1 1)) 1
     (multiset '()) -1}))

(def sphere-polynomial
  (Polynomial.
    qq
    {(multiset '(0 0)) 1
     (multiset '(1 1)) 1
     (multiset '(2 2)) 1
     (multiset '()) -1}))

; Use this method in order to apply polynomials to ordered collections of elements
(defn apply-polynomial
  [polynomial coll]

  (let [ring (ring-of-coefficients polynomial)
        add (additive-semigroup ring)
        mul (multiplicative-semigroup ring)
        data (.data polynomial)]
    (apply-monoid
      add
      (map
        (fn [[term coefficient]]
          (if (empty? term)
            coefficient
            (let [term-product (apply-semigroup
                                 mul
                                 (map
                                   (fn [index]
                                     (nth coll index))
                                   term))]
              (mul (list coefficient term-product)))))
        data))))

; Get all variables of a given polynomial
(defn polynomial-variables
  [polynomial]

  (apply union (map support (terms polynomial))))

(defn polynomial-variables-count
  [polynomial]

  (count (polynomial-variables polynomial)))

(defn polynomial-degree
  [polynomial]

  (apply
    max
    (map count (.data polynomial))))

(def term-count
  (comp count terms))

; Superscript digits
(def superscript-digit-strings
  ["⁰" "¹" "²" "³" "⁴" "⁵" "⁶" "⁷" "⁸" "⁹"])

(defn superscriptize
  [num]

  (apply
    str
    (map
      (fn [char]
        (let [c (Integer/parseInt (.toString char))]
          (nth superscript-digit-strings c)))
      (seq num))))

(def alphabet
  ["a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l" "m" "n"
   "o" "p" "q" "r" "s" "t" "u" "v" "w" "x" "y" "z"])

(defn term-to-string
  [coll]

  (apply
    str
    (map
      (fn [i]
        (str
          (nth alphabet i)
          (let [exponent (multiplicity coll i)]
            (if (= exponent 1)
              ""
              (superscriptize (str exponent))))))
      (sort < (support coll)))))

(defn display-polynomial
  [polynomial]

  (apply
    str
    (interpose
      " + "
      (map
        (fn [[term coefficient]]
          (str
            (if (and (= coefficient 1) (not (empty? term)))
              ""
              coefficient)
            (term-to-string term)))
        (.data polynomial)))))

; Ontology of polynomials
; Polynomials can be classified in a rather similar manner to multiset systems
(defmulti polynomial? type)

(defmethod polynomial? :default
  [func] false)

(defmethod polynomial? Polynomial
  [func] true)

(defn univariate-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (<= (polynomial-variables polynomial) 1)))

(defn linear-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (every? unique-universal? (terms polynomial))))

(def linear-univariate-polynomial?
  (intersection
    linear-polynomial?
    univariate-polynomial?))

(defn monomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (term-count polynomial) 1)))

(defn binomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (term-count polynomial) 2)))

(defn trinomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (term-count polynomial) 3)))

(defn quadrinomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (term-count polynomial) 4)))

(defn homogeneous-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (equal-seq? (map count (terms polynomial)))))

(defn quadratic-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (polynomial-degree 2))))

(defn cubic-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (polynomial-degree polynomial) 3)))

(defn quartic-polynomial?
  [polynomial]

  (and
    (polynomial? polynomial)
    (= (polynomial-degree polynomial) 4)))

(def univariate-quadratic-polynomial?
  (intersection
    quadratic-polynomial?
    univariate-polynomial?))

(def univariate-cubic-polynomial?
  (intersection
    cubic-polynomial?
    univariate-polynomial?))

(def univariate-quadratic-polynomial?
  (intersection
    quartic-polynomial?
    univariate-polynomial?))

(defn quadratic-form?
  [polynomial]

  (and
    (polynomial? polynomial)
    (every?
      (fn [term]
        (= (count term) 2))
      (terms polynomial))))

(defn cubic-form?
  [polynomial]

  (and
    (polynomial? polynomial)
    (every?
      (fn [term]
        (= (count term) 3))
      (terms polynomial))))

(defn quartic-form?
  [polynomial]

  (and
    (polynomial? polynomial)
    (every?
      (fn [term]
        (= (count term) 4))
      (terms polynomial))))







