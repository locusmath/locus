(ns locus.algebra.category.hom.dhom
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.quiver.diset.core.object Diset]
           [locus.set.quiver.diset.core.morphism Difunction]
           (locus.set.logic.core.set SeqableUniversal)))

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
