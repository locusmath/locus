(ns locus.elementary.hom.functional.bhom
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.gem.core.object :refer :all]
            [locus.elementary.hom.functional.sethom :refer :all])
  (:import [locus.elementary.bijection.core.object Bijection]
           [locus.elementary.gem.core.object Gem]
           (locus.elementary.logic.base.core SeqableUniversal)))

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