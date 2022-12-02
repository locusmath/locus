(ns locus.elementary.category.hom.bhom
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.elementary.category.hom.sethom :refer :all]
            [locus.quiver.base.core.protocols :refer :all])
  (:import [locus.elementary.bijection.core.object Bijection]
           [locus.elementary.bijection.core.morphism Gem]
           (locus.base.logic.core.set SeqableUniversal)))

; This file supports the creation of hom classes
;  in the topos of bijections Sets^(K_2).

(defn in-bijective-hom-class?
  [morphism a b]

  (and
    (= (source-object morphism) a)
    (= (target-object morphism) b)))

(defn number-of-bijection-homomorphisms
  [a b]

  (.pow (BigInteger/valueOf (bijection-cardinality b)) (bijection-cardinality a)))

(defn bijection-hom
  [a b]

  (SeqableUniversal.
    (fn [func]
      (and
        (gem? func)
        (in-bijective-hom-class? func a b)))
    (map
      (fn [mapping]
        (interrelational-morphism
          a
          b
          mapping))
      (enumerate-mappings
        (underlying-relation a)
        (underlying-relation b)))
    {:count (number-of-bijection-homomorphisms a b)}))

; Now we will compute the set of all bijection isomorphisms
(defn bijection-isomorphisms
  [a b]

  (let [first-cardinality (bijection-cardinality a)
        second-cardinality (bijection-cardinality b)]
    (if (= first-cardinality second-cardinality)
      (SeqableUniversal.
       (fn [func]
         (and
           (gem? func)
           (in-bijective-hom-class? func a b)))
       (map
         (fn [mapping]
           (interrelational-morphism
             a
             b
             mapping))
         (enumerate-injective-mappings
           (underlying-relation a)
           (underlying-relation b)))
       {:count (factorial (bijection-cardinality a))})
      #{})))