(ns locus.set.square.core.util
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.mapping.effects.global.identity :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.copresheaf.incidence.core.object :refer :all]
            [locus.set.tree.cospan.core.object :refer :all]
            [locus.set.tree.triangle.core.object :refer :all])
  (:import (locus.set.mapping.effects.global.identity IdentityFunction)
           (locus.set.mapping.general.core.object SetFunction)
           (locus.set.square.core.morphism SetSquare)
           (locus.set.tree.triangle.core.object SetTriangle)
           (locus.set.tree.cospan.core.object Cospan)
           (locus.set.copresheaf.incidence.core.object Span)))

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
(defn cartesian-square
  [^Cospan cospan]

  (let [cospan1 (first-cospan-function cospan)
        cospan2 (second-cospan-function cospan)
        [predecessor1 predecessor2] (fiber-product-projections cospan1 cospan2)]
    (SetSquare.
      predecessor1
      cospan2
      predecessor1
      cospan1)))

; A cocartesian diamond of a span copresheaf
(defn cocartesian-square
  [^Span span]

  (let [span1 (edge-function span)
        span2 (vertex-function span)
        [successor1 successor2] (fiber-coproduct-projections span1 span2)]
    (SetSquare.
      span1
      successor2
      span2
      successor1)))

; Get triagnles from diamonds
(defn input-action-triangle
  [^SetSquare diamond]

  (SetTriangle.
    (target-object diamond)
    (input-set-function diamond)))

(defn output-action-triangle
  [^SetSquare diamond]

  (SetTriangle.
    (output-set-function diamond)
    (source-object diamond)))

(defn set-square-triangles
  [^SetSquare diamond]

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
    (SetSquare.
      source-function
      target-function
      input-function
      output-function)))

(defn to-input-action-square
  [^SetTriangle triangle]

  (input-action-square (.f triangle) (.g triangle)))

(defn to-output-action-square
  [^SetTriangle triangle]

  (output-action-square (.g triangle) (.f triangle)))

; Reduce diamonds to simpler copresheaves if possible
(defn reduce-square
  [diamond]

  (let [id1 (intrinsic-identity-function? (first-function diamond))
        id2 (intrinsic-identity-function? (second-function diamond))]
    (cond
      (and id1 id2) (source-object diamond)
      id1 (SetTriangle. (second-function diamond) (source-object diamond))
      id2 (SetTriangle. (target-object diamond) (first-function diamond))
      :else diamond)))
