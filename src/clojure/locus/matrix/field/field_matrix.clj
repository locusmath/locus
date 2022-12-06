(ns locus.matrix.field.field-matrix
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semifield.core.object :refer :all]
            [locus.additive.field.core.object :refer :all])
  (:import [org.apache.commons.math3.linear FieldLUDecomposition LUDecomposition FieldMatrix RealMatrix Array2DRowRealMatrix Array2DRowFieldMatrix Array2DRowFieldMatrix FieldLUDecomposition MatrixUtils]
           [org.apache.commons.math3.complex Complex]
           (locus.algebra.group.core.object Group)
           (locus.algebra.semigroup.monoid.object Monoid)))

; Field matrices are primarily provided by the apache commons math library. In order to make
; interoperability with the apache commons math field matrices more accessible, we
; present a selection of methods which will create a common framework for interoperability
; between Locus matrices and apache commons math structures.

; Print methods
(defmethod print-method RealMatrix [^RealMatrix v ^java.io.Writer w]
  (.write w (str "#C" (.toString v))))

(defmethod print-method RealMatrix [^FieldMatrix v ^java.io.Writer w]
  (.write w (str "#C" (.toString v))))

; Generic arithmetic
(defmethod add [FieldMatrix FieldMatrix]
  [^FieldMatrix a, ^FieldMatrix b]

  (.add a b))

(defmethod multiply [FieldMatrix FieldMatrix]
  [^FieldMatrix a, ^FieldMatrix b]

  (.multiply a b))

(defmethod add [RealMatrix RealMatrix]
  [^RealMatrix a, ^RealMatrix b]

  (.add a b))

(defmethod multiply [RealMatrix RealMatrix]
  [^RealMatrix a, ^RealMatrix b]

  (.multiply a  b))

; Create real and complex matrices through the apache commons math library
(defn real-matrix
  [coll]

  (Array2DRowRealMatrix.
    (into-array
      (Class/forName "[D")
      (map double-array coll))))

; This uses the fact that the JVM does not reify generics in the runtime
(defn complex-matrix
  [coll]

  (Array2DRowFieldMatrix.
    (into-array
      (map
        into-array
        coll))))

; Check for a real matrix
(defn field-matrix?
  [matrix]

  (or
    (instance? RealMatrix matrix)
    (instance? FieldMatrix matrix)))

(defn real-matrix?
  [matrix]

  (instance? RealMatrix matrix))

(defn invertible-real-matrix?
  [matrix]

  (and
    (real-matrix? matrix)
    (.isSquare matrix)
    (let [det (.getDeterminant (LUDecomposition. matrix))]
      (not= det 0))))

(defn unimodular-real-matrix?
  [matrix]

  (and
    (real-matrix? matrix)
    (.isSquare matrix)
    (let [det (.getDeterminant (LUDecomposition. matrix))]
      (= det 1))))

(defn invertible-field-matrix?
  [matrix]

  (or
    (invertible-real-matrix? matrix)
    (and
      (instance? FieldMatrix matrix)
      (.isSquare matrix)
      (let [det (.getDeterminant (FieldLUDecomposition. matrix))]
       (not= det 0)))))

(defn group-of-real-matrices
  [n coll]

  (Group.
    coll
    (fn [[a b]] (.multiply a b))
    (MatrixUtils/createRealIdentityMatrix n)
    (fn [matrix] (MatrixUtils/inverse matrix))))

(defn real-general-linear-group
  [n]

  (group-of-real-matrices
    n
    (fn [matrix]
      (and
        (invertible-real-matrix? matrix)
        (= (.getRowDimension matrix) (.getColumnDimension matrix) n)))))

(defn real-special-linear-group
  [n]

  (group-of-real-matrices
    n
    (fn [matrix]
      (and
        (unimodular-real-matrix? matrix)
        (= (.getRowDimension matrix) (.getColumnDimension matrix) n)))))

(defn real-matrix-addition-group
  [n]

  (Group.
    (intersection
      real-matrix?
      (fn [matrix] (= (.getRowDimension matrix) (.getColumnDimension matrix) n)))
    (fn [[a b]]
      (.add a b))
    (MatrixUtils/createRealDiagonalMatrix
      (into-array Double/TYPE (repeat n 0)))
    (fn [matrix]
      (.scalarMultiply matrix -1))))

(defn real-matrix-multiplication-monoid
  [n]

  (Monoid.
    (intersection
      real-matrix?
      (fn [matrix] (= (.getRowDimension matrix) (.getColumnDimension matrix) n)))
    (fn [[a b]]
      (.add a b))
    (MatrixUtils/createRealIdentityMatrix n)))

(defn real-matrix-ring
  [n]

  (make-ring
    (real-matrix-addition-group n)
    (real-matrix-multiplication-monoid n)))



