(ns locus.elementary.category.hom.dhom
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.category.hom.sethom :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all])
  (:import [locus.elementary.diset.core.object Diset]
           [locus.elementary.difunction.core.object Difunction]
           (locus.base.logic.core.set SeqableUniversal)))

; This file supports the creation of hom classes in the topos Sets^2.
; These hom classes are simply defined by doubling up hom classes in Sets.

; We can now begin to create an enumeration of set pair homomorphisms
(defn in-diset-hom-class?
  [func a b]

  (let [f (first-function func)
        g (second-function func)]
    (and
      (in-hom-class? f (first-set a) (first-set b))
      (in-hom-class? g (second-set a) (second-set b)))))

(defn number-of-diset-mappings
  [a b]

  (* (number-of-mappings (first-set a) (first-set b))
     (number-of-mappings (second-set a) (second-set b))))

(defn diset-hom
  [a b]

  (SeqableUniversal.
    (fn [func]
      (and
        (difunction? func)
        (in-diset-hom-class? func a b)))
    (let [a1 (first-set a)
          a2 (second-set a)
          b1 (first-set b)
          b2 (second-set b)
          function-pairs (seqable-cartesian-product
                           (set-hom a1 b1)
                           (set-hom a2 b2))]
      (map
        (fn [function-pair]
          (Difunction. (first function-pair) (second function-pair)))
        function-pairs))
    {:count (number-of-diset-mappings a b)}))

; We need to get the isomorphisms of two set pairs using the same idea
(defn diset-isomorphisms
  [a b]

  (if (not= (cardinality-pair a) (cardinality-pair b))
    #{}
    (SeqableUniversal.
     (fn [func]
       (and
         (invertible-difunction? func)
         (in-diset-hom-class? func a b)))
     (map
       (fn [pair]
         (Difunction. (first pair) (second pair)))
       (seqable-cartesian-product
         (bijective-set-hom (first-set a) (first-set b))
         (bijective-set-hom (second-set a) (second-set b))))
     {:count (* (factorial (count (first-set a)))
                (factorial (count (second-set a))))})))

; Injective diset morphisms
(defn injective-diset-hom
  [a b]

  (SeqableUniversal.
    (fn [func]
      (and
        (injective-difunction? func)
        (in-diset-hom-class? func a b)))
    (map
      (fn [pair]
        (Difunction. (first pair) (second pair)))
      (seqable-cartesian-product
        (injective-set-hom (first-set a) (first-set b))
        (injective-set-hom (second-set a) (second-set b))))
    {:count (* (number-of-injections (first-set a) (first-set b))
               (number-of-injections (second-set a) (second-set b)))}))

; Surjective diset morphisms
(defn surjective-diset-hom
  [a b]

  (SeqableUniversal.
    (fn [func]
      (and
        (surjective-difunction? func)
        (in-diset-hom-class? func a b)))
    (map
      (fn [pair]
        (Difunction. (first pair) (second pair)))
      (seqable-cartesian-product
        (surjective-set-hom (first-set a) (first-set b))
        (surjective-set-hom (second-set a) (second-set b))))
    {:count (* (number-of-surjections (first-set a) (first-set b))
               (number-of-surjections (second-set a) (second-set b)))}))
