(ns locus.algebra.category.hom.bhom
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.copresheaf.bijection.core.morphism :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.copresheaf.bijection.core.object Bijection]
           [locus.set.copresheaf.bijection.core.morphism Gem]
           (locus.set.logic.core.set SeqableUniversal)))

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