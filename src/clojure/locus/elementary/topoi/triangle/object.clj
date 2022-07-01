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

; The two function components of the triangle copresheaf
(defn prefunction
  [^TriangleCopresheaf triangle]

  (.g triangle))

(defn postfunction
  [^TriangleCopresheaf triangle]

  (.f triangle))

(defn compfunction
  [^TriangleCopresheaf triangle]

  (compose (.f triangle) (.g triangle)))

(defn triangle-source
  [^TriangleCopresheaf triangle]

  (source-object (prefunction triangle)))

(defn triangle-middle-set
  [^TriangleCopresheaf triangle]

  (target-object (prefunction triangle)))

(defn triangle-target
  [^TriangleCopresheaf triangle]

  (target-object (postfunction triangle)))

; Input and output action triangles
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

; Convert triangles into diamonds
(defn to-input-action-diamond
  [^TriangleCopresheaf triangle]

  (input-action-diamond (.f triangle) (.g triangle)))

(defn to-output-action-diamond
  [^TriangleCopresheaf triangle]

  (output-action-diamond (.g triangle) (.f triangle)))

; Ontology of triangle copresheaves
(defn triangle?
  [x]

  (= (type x) TriangleCopresheaf))

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
