(ns locus.algebra.category.system.morphism-system
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.semigroup.core.object Semigroup)))

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




