(ns locus.set.copresheaf.dependency.difunction.diset-pair
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.diset.core.object :refer :all])
  (:import (locus.set.quiver.diset.core.object Diset)))

; Ontology of pairs of disets
; Given a difunction (f,g) then it induces naturally a pair of disets from
; the diset component of the two function elements of the difunction.
(defn diset-pair?
  [a b]

  (and
    (diset? a)
    (diset? b)))

(defn equal-diset-pair?
  [a b]

  (and
    (diset? a)
    (diset? b)
    (= a b)))

(defn common-input-diset-pair?
  [a b]

  (and
    (diset? a)
    (diset? b)
    (= (first-set a) (first-set b))))

(defn common-output-diset-pair?
  [a b]

  (and
    (diset? a)
    (diset? b)
    (= (second-set a) (second-set b))))

(defn comparable-disets?
  [a b]

  (and
    (diset? a)
    (diset? b)
    (or (superdiset? (list a b))
        (superdiset? (list b a)))))


