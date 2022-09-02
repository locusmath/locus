(ns locus.elementary.topoi.triangle.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all])
  (:import (locus.elementary.diamond.core.object Diamond)))

; Objects of the elementary topos Sets^(T_3) of copresheaves over the total
; order with three elements. These can be formed from copresheaves in the
; fundamental topos Sets^[1,2,1] in two different ways.
(deftype TriangleCopresheaf [f g])

; Special types of triangle copresheaves
(defn trivial-triangle
  [coll]

  (TriangleCopresheaf. (identity-function coll) (identity-function coll)))

(defn prefunction-trivial-triangle
  [func]

  (TriangleCopresheaf. func (identity-function (source-object func))))

(defn postfunction-trivial-triangle
  [func]

  (TriangleCopresheaf. (identity-function (target-object func)) func))

; Function components of triangles
(defn prefunction
  [^TriangleCopresheaf triangle]

  (.g triangle))

(defn postfunction
  [^TriangleCopresheaf triangle]

  (.f triangle))

(defn compfunction
  [^TriangleCopresheaf triangle]

  (compose (.f triangle) (.g triangle)))

; Set components of triangles
(defn triangle-source
  [^TriangleCopresheaf triangle]

  (source-object (prefunction triangle)))

(defn triangle-middle-set
  [^TriangleCopresheaf triangle]

  (target-object (prefunction triangle)))

(defn triangle-target
  [^TriangleCopresheaf triangle]

  (target-object (postfunction triangle)))

; Get the kernels of the triangle
(defn triangle-source-kernels
  [^TriangleCopresheaf triangle]

  (list
    (function-kernel (prefunction triangle))
    (function-kernel (compfunction triangle))))

(defn triangle-target-images
  [^TriangleCopresheaf triangle]

  (list
    (function-image (postfunction triangle))
    (function-image (compfunction triangle))))

; Input and output action triangles of diamond copresheaves
(defn input-action-triangle
  [^Diamond diamond]

  (TriangleCopresheaf.
    (target-object diamond)
    (input-set-function diamond)))

(defn output-action-triangle
  [^Diamond diamond]

  (TriangleCopresheaf.
    (output-set-function diamond)
    (source-object diamond)))

(defn diamond-triangles
  [^Diamond diamond]

  (list
    (input-action-triangle diamond)
    (output-action-triangle diamond)))

(defn combine-triangles
  [^TriangleCopresheaf in, ^TriangleCopresheaf out]

  (let [target-function (.-f in)
        input-function (.-g in)
        output-function (.-f out)
        source-function (.-g out)]
    (Diamond.
      source-function
      target-function
      input-function
      output-function)))

; Convert triangles into diamonds
(defn to-input-action-diamond
  [^TriangleCopresheaf triangle]

  (input-action-diamond (.f triangle) (.g triangle)))

(defn to-output-action-diamond
  [^TriangleCopresheaf triangle]

  (output-action-diamond (.g triangle) (.f triangle)))

; Products and coproducts in the topoi of triangle copresheaves
(defmethod product TriangleCopresheaf
  [& args]

  (TriangleCopresheaf.
    (apply product (map postfunction args))
    (apply product (map prefunction args))))

(defmethod coproduct TriangleCopresheaf
  [& args]

  (TriangleCopresheaf.
    (apply coproduct (map postfunction args))
    (apply coproduct (map prefunction args))))

; Compute the substructure of a triangle copresheaf
(defn subtriangle?
  [triangle new-source new-middle new-target]

  (and
    (subfunction? (postfunction triangle) new-middle new-target)
    (subfunction? (prefunction triangle) new-source new-middle)))

(defn subtriangle
  [triangle new-source new-middle new-target]

  (TriangleCopresheaf.
    (subfunction (postfunction triangle) new-middle new-target)
    (subfunction (prefunction triangle) new-source new-middle)))

; Compute the quotients of a triangle copresheaf
(defn triangle-congruence?
  [triangle source-partition middle-partition target-partition]

  (and
    (io-relation? (postfunction triangle) middle-partition target-partition)
    (io-relation? (prefunction triangle) source-partition middle-partition)))

(defn quotient-triangle
  [triangle source-partition middle-partition target-partition]

  (TriangleCopresheaf.
    (quotient-function (postfunction triangle) middle-partition target-partition)
    (quotient-function (prefunction triangle) source-partition middle-partition)))

; Ontology of triangle copresheaves
(defn triangle?
  [x]

  (= (type x) TriangleCopresheaf))

(defn prefunction-invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (prefunction x))))

(defn postfunction-invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (postfunction x))))

(defn invertible-triangle?
  [x]

  (and
    (triangle? x)
    (invertible? (prefunction x))
    (invertible? (postfunction x))))

; Identity functions are special cases of invertible ones
(defn prefunction-trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (prefunction x))))

(defn postfunction-trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (postfunction x))))

(defn trivial-triangle?
  [x]

  (and
    (triangle? x)
    (identity-function? (prefunction x))
    (identity-function? (postfunction x))))