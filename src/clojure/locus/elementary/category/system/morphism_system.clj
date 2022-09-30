(ns locus.elementary.category.system.morphism-system
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.element.object :refer :all]))

; Let C be a category, and Arrows(C) its set of morphisms. Then the power set P(Arrows(C)) consists of
; the set of all morphism systems of C. Morphism systems are used throughout category theory,
; for example in homological algebra we use chains of morphisms such as exact sequences and chain
; complexes to better understand objects of abelian categories. In Grothendeick topos theory, we use
; common output morphism systems to define coverings of sites which generalize sheaves, and so on.
; A complete ontology of category theory must include an ontology of morphism systems.

(def morphism-system?
  (power-set morphism?))

(defn parallel-morphism-system?
  [coll]

  (and
    (morphism-system? coll)
    (equal-seq? (map underlying-transition coll))))

(defn common-input-morphism-system?
  [coll]

  (and
    (morphism-system? coll)
    (equal-seq? (map source-object coll))))

(defn common-output-morphism-system?
  [coll]

  (and
    (morphism-system? coll)
    (equal-seq? (map target-object coll))))

(def endomorphism-system?
  (power-set endomorphism?))

(defn compose-morphism-systems
  [ms1 ms2]

  (set
    (for [[a b] (cartesian-product ms1 ms2)
          :when (composable-morphisms? a b)]
      (compose a b))))

(defn semigroup-of-morphism-systems
  [category]

  (Semigroup.
    (->PowerSet (category-morphisms category))
    (fn [[a b]]
      (compose-morphism-systems a b))))




