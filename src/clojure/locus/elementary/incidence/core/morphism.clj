(ns locus.elementary.incidence.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.incidence.core.object :refer :all])
  (:import (locus.elementary.incidence.core.object Span)))

; Morphisms in the topos Sets^{[1,2]} of span copresheaves
; Morphisms of spans have three components: a flag component function, an edge component function,
; and a vertex component function. Together they make up the data of a natural transformation.
(deftype MorphismOfSpans [source-span target-span ffn efn vfn]
  AbstractMorphism
  (source-object [this]
    source-span)
  (target-object [this]
    target-span))

; Composition and identities in the topos of span copresheaves
(defmethod compose* MorphismOfSpans
  [^MorphismOfSpans a, ^MorphismOfSpans b]

  (MorphismOfSpans.
    (source-object b)
    (target-object a)
    (comp (.ffn a) (.ffn b))
    (comp (.efn a) (.efn b))
    (comp (.vfn a) (.vfn b))))

(defmethod identity-morphism Span
  [^Span span]

  (MorphismOfSpans.
    span
    span
    (identity-function (span-flags span))
    (identity-function (span-edges span))
    (identity-function (span-vertices span))))

; Ontology of morphisms of spans
(defn morphism-of-spans?
  [morphism]

  (= (type morphism) MorphismOfSpans))