(ns locus.elementary.cospan.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.cospan.core.object :refer :all])
  (:import (locus.elementary.cospan.core.object Cospan)))

; Morphisms in the topos of cospan copresheaves Sets^[2,1]
; Morphisms of cospans have three components: a first source function, a second source function,
; and a target function. Together they make up the components of a natural transformation.
(deftype MorphismOfCospans [source-cospan target-cospan afn bfn cfn]
  AbstractMorphism
  (source-object [this]
    source-cospan)
  (target-object [this]
    target-cospan))

; Composition and identities in the topos of cospan copresheaves
(defmethod compose* MorphismOfCospans
  [^MorphismOfCospans a, ^MorphismOfCospans b]

  (MorphismOfCospans.
    (source-object b)
    (target-object a)
    (comp (.afn a) (.afn b))
    (comp (.bfn a) (.bfn b))
    (comp (.cfn a) (.cfn b))))

(defmethod identity-morphism Cospan
  [^Cospan cospan]

  (MorphismOfCospans.
    cospan
    cospan
    (identity-function (first-cospan-source cospan))
    (identity-function (second-cospan-source cospan))
    (identity-function (cospan-target cospan))))

; Ontology of morphisms of cospans
(defn morphism-of-cospans?
  [cospan]

  (= (type cospan) MorphismOfCospans))