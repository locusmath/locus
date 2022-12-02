(ns locus.matrix.semiring.semiring-matrix
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.vertices :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.matrix.combinatorics.adjacency-matrix :refer :all])
  (:import [org.apache.commons.math3.linear AnyMatrix]))

; The apache commons math library only supports matrices over
; fields. We need to extend that in order to support matrices
; over semirings. These semiring matrices therefore can be defined
; over any Locus semiring.

(deftype SemiringMatrix [semiring data]
  AnyMatrix
  (getColumnDimension [this]
    (if (empty? data)
      0
      (count (first data))))
  (getRowDimension [this]
    (count data))
  (isSquare [this]
    (= (.getColumnDimension this) (.getRowDimension this)))

  java.lang.Object
  (equals [this x]
    (and
      (instance? SemiringMatrix x)
      (.equals (.semiring this) (.semiring x))
      (.equals (.data this) (.data x))))
  (toString [this]
    (apply
      str
      (interpose
        "\n   "
        (map #(.toString (seq %)) data)))))

(defmethod print-method SemiringMatrix [^SemiringMatrix v ^java.io.Writer w]
  (.write w (.toString v)))

; Get the rows and columns of a matrix
(defn get-row
  [^SemiringMatrix matrix, n]

  (nth (.data matrix) n))

(defn get-column
  [^SemiringMatrix matrix, n]

  (map
    (fn [i]
      (nth (nth (.data matrix) i) n))
    (range (.getRowDimension matrix))))

; Construct matrices over the t2 semiring
(defn binary-matrix
  [coll]

  (SemiringMatrix. t2 coll))

; Construct matrices over the natural semiring
(defn natural-matrix
  [coll]

  (SemiringMatrix. nn coll))

; The most basic example of a matrix constructed over a ring
(defn integral-matrix
  [coll]

  (SemiringMatrix. zz coll))

; Convert binary relations into matrices by their adjacency matrices
; this naturally produces a semigroup isomorphism from the multiplicative
; semigroup of all matrices over the t2 semiring to the semigroup of all
; binary relations on a set under composition.
(defn relation->matrix
  [rel]

  (binary-matrix (adjacency-matrix rel)))

(defn multirelation->matrix
  [rel]

  (natural-matrix (adjacency-matrix rel)))

; Transposition is a basic operation which is also applicable to matrices
(defn transpose-matrix
  [matrix]

  (SemiringMatrix.
    (.semiring matrix)
    (build-matrix
      (fn [x y]
        (nth (nth (.data matrix) y) x))
      (.getColumnDimension matrix)
      (.getRowDimension matrix))))

; Dot products can be used to define matrix multiplication
(defn semiring-dot-product
  [ring a b]

  (let [add (additive-semigroup ring)
        mul (multiplicative-semigroup ring)]
    (apply-semigroup
      add
      (map
        (fn [i]
          (apply-semigroup mul [(nth a i) (nth b i)]))
        (range (count a))))))

; Arithmetical properties of semiring matrices
(defn zero-matrix
  [semiring n]

  (SemiringMatrix.
    semiring
    (let [zero (identity-element (additive-semigroup semiring))]
      (build-square-matrix
        (fn [x y]
          zero)
        n))))

(defn scale-matrix
  [matrix scalar-factor]

  (let [ring (.semiring matrix)
        mul (multiplicative-semigroup ring)]
    (SemiringMatrix.
      ring
      (build-matrix
        (fn [i j]
          (mul
            (list
              scalar-factor
              (nth (nth (.data matrix) i) j))))
        (.getRowDimension matrix)
        (.getColumnDimension matrix)))))

(defmethod add [SemiringMatrix SemiringMatrix]
  [m1 m2]

  (let [ring (.semiring m1)
        add (additive-semigroup ring)]
    (SemiringMatrix.
      ring
      (build-matrix
        (fn [x y]
          (add
            (list
              (nth (nth (.data m1) x) y)
              (nth (nth (.data m2) x) y))))
        (.getRowDimension m1)
        (.getColumnDimension m1)))))

(defmethod multiply [SemiringMatrix SemiringMatrix]
  [m1 m2]

  (let [ring (.semiring m1)
        mul (multiplicative-semigroup ring)]
    (SemiringMatrix.
      ring
      (build-matrix
        (fn [i j]
          (let [a-row (get-row m1 i)
                b-column (get-column m2 j)]
            (semiring-dot-product ring a-row b-column)))
        (.getRowDimension m1)
        (.getColumnDimension m2)))))

(defmethod negate SemiringMatrix
  [matrix]

  (let [ring (.semiring matrix)
        inv (additive-inverse-function ring)]
    (SemiringMatrix.
      ring
      (build-matrix
        (fn [i j]
          (inv (nth (nth (.data matrix) i) j)))
        (.getRowDimension matrix)
        (.getColumnDimension matrix)))))

; Create a square matrix semigroup of a semiring
(defn enumerate-semiring-square-matrices
  [ring n]

  (map
    (fn [coll]
      (SemiringMatrix.
        ring
        (map
          (fn [i]
            (map
              (fn [j]
                (nth coll (+ (* i n) j)))
              (range n)))
          (range n))))
    (cartesian-power (underlying-set ring) (* n n))))

(defn semiring-matrix-classifier
  [ring n]

  (let [pred (fn [i]
               (and
                 (= (type i) SemiringMatrix)
                 (= (.-semiring ^SemiringMatrix i) ring)
                 (= (.getRowDimension i)
                    (.getColumnDimension i)
                    n)))]
    (if (seqable-universal? (underlying-set ring))
      (->SeqableUniversal
        pred
        (enumerate-semiring-square-matrices ring n)
        {})
      pred)))

(defn matrix-multiplication
  [semiring n]

  (->Semigroup
    (semiring-matrix-classifier semiring n)
    (fn [[a b]]
      (* a b))))

(defn matrix-addition
  [semiring n]

  (if (intrinsic-ring? semiring)
    (->Group
      (semiring-matrix-classifier semiring n)
      (fn [[a b]]
        (+ a b))
      (zero-matrix semiring n)
      (fn [a] (- a)))
    (->Monoid
      (semiring-matrix-classifier semiring n)
      (fn [[a b]]
        (+ a b))
      (zero-matrix semiring n))))

(defn matrix-semiring
  [semiring n]

  (make-ring
    (matrix-addition semiring n)
    (matrix-multiplication semiring n)))

(defmethod get-semiring SemiringMatrix
  [^SemiringMatrix matrix]

  (matrix-semiring
    (.semiring matrix)
    (.getRowDimension matrix)))





