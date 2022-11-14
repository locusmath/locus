(ns locus.elementary.lattice.algebra.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.elementary.dependency.nset.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.difunction.core.object Difunction)
           (locus.elementary.bijection.core.morphism Gem)
           (locus.elementary.dependency.nset.object NSet)
           (locus.elementary.lattice.core.object Lattice)))

; Subalgebras and congruences in the topos Sets^2
(defmethod sub Diset
  [pair]

  (Lattice.
    (seqable-diset-subalgebras pair)
    join-set-pairs
    meet-set-pairs))

(defmethod con Diset
  [pair]

  (Lattice.
    (seqable-diset-congruences pair)
    join-set-pair-congruences
    meet-set-pair-congruences))

; Subalgebras and congruences of bijections
(defmethod sub Bijection
  [func]

  (Lattice.
    (all-subbijections func)
    join-set-pairs
    meet-set-pairs))

(defmethod con Bijection
  [func]

  (Lattice.
    (set (enumerate-set-partitions (underlying-relation func)))
    join-set-partitions
    meet-set-partitions))

; Subalgebras and congruences of quivers
(defmethod sub :locus.elementary.quiver.core.object/quiver
  [quiv]

  (Lattice.
    (subquivers quiv)
    join-set-pairs
    meet-set-pairs))

(defmethod con :locus.elementary.quiver.core.object/quiver
  [quiv]

  (Lattice.
    (quiver-congruences quiv)
    (fn [& congruences]
      (let [[new-in new-out] (apply join-set-pair-congruences congruences)]
        (quiver-congruence-closure quiv new-in new-out)))
    meet-set-pair-congruences))

; Subalgebras and congruencse of difunctions
(defmethod sub Difunction
  [x]

  (product
    (sub (first-function x))
    (sub (second-function x))))

(defmethod con Difunction
  [x]

  (product
    (con (first-function x))
    (con (second-function x))))

; Subalgebras and congruences of morphisms of bijections
(defmethod sub Gem
  [gem]

  (sub (interrelational-component gem)))

(defmethod con Gem
  [gem]

  (con (interrelational-component gem)))

; Subobjects and congruences of nsets
(defmethod sub NSet
  [nset]

  (->Lattice
    (nset-subalgebras nset)
    join-set-sequences
    meet-set-sequences))

(defmethod con NSet
  [nset]

  (->Lattice
    (nset-congruences nset)
    join-set-sequence-congruences
    meet-set-sequence-congruences))

