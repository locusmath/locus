(ns locus.elementary.difunction.core.diset-pair
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all])
  (:import (locus.elementary.diset.core.object Diset)))

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


