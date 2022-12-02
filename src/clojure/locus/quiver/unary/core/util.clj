(ns locus.quiver.unary.core.util
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.quiver.unary.core.morphism :refer :all]
            [locus.elementary.incidence.core.object :refer :all]
            [locus.elementary.cospan.core.object :refer :all]
            [locus.elementary.triangle.core.object :refer :all])
  (:import (locus.base.effects.global.identity IdentityFunction)
           (locus.base.function.core.object SetFunction)
           (locus.elementary.cospan.core.object Cospan)
           (locus.elementary.incidence.core.object Span)
           (locus.elementary.triangle.core.object SetTriangle)))

; The upper cospan and the lower span in the topos Sets^[1,2,1]
; relates it to te topoi Sets^[1,2] and Sets^[2,1]
(defn upper-cospan
  [func]

  (cospan
    (second-function func)
    (target-object func)))

(defn lower-span
  [func]

  (span
    (first-function func)
    (source-object func)))

; The cartesian diamond of a cospan copresheaf
(defn cartesian-diamond
  [^Cospan cospan]

  (let [cospan1 (first-cospan-function cospan)
        cospan2 (second-cospan-function cospan)
        [predecessor1 predecessor2] (fiber-product-projections cospan1 cospan2)]
    (Diamond.
      predecessor1
      cospan2
      predecessor1
      cospan1)))

; A cocartesian diamond of a span copresheaf
(defn cocartesian-diamond
  [^Span span]

  (let [span1 (edge-function span)
        span2 (vertex-function span)
        [successor1 successor2] (fiber-coproduct-projections span1 span2)]
    (Diamond.
      span1
      successor2
      span2
      successor1)))

; Get triagnles from diamonds
(defn input-action-triangle
  [^Diamond diamond]

  (SetTriangle.
    (target-object diamond)
    (input-set-function diamond)))

(defn output-action-triangle
  [^Diamond diamond]

  (SetTriangle.
    (output-set-function diamond)
    (source-object diamond)))

(defn diamond-triangles
  [^Diamond diamond]

  (list
    (input-action-triangle diamond)
    (output-action-triangle diamond)))

; Create diamond from pairs of triangles
(defn combine-triangles
  [^SetTriangle in, ^SetTriangle out]

  (let [target-function (.-f in)
        input-function (.-g in)
        output-function (.-f out)
        source-function (.-g out)]
    (Diamond.
      source-function
      target-function
      input-function
      output-function)))

(defn to-input-action-diamond
  [^SetTriangle triangle]

  (input-action-diamond (.f triangle) (.g triangle)))

(defn to-output-action-diamond
  [^SetTriangle triangle]

  (output-action-diamond (.g triangle) (.f triangle)))

; Reduce diamonds to simpler copresheaves if possible
(defn reduce-diamond
  [diamond]

  (let [id1 (intrinsic-identity-function? (first-function diamond))
        id2 (intrinsic-identity-function? (second-function diamond))]
    (cond
      (and id1 id2) (source-object diamond)
      id1 (SetTriangle. (second-function diamond) (source-object diamond))
      id2 (SetTriangle. (target-object diamond) (first-function diamond))
      :else diamond)))
