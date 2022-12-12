(ns locus.set.quiver.relation.quaternary.qr
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]))

; A quaternary relation is a set of ordered quadruples
; The theory of quaternary relations is even less developed than the theory of ternary
; relations, which in turn is less developed than the theory of binary relations. However,
; there are a number of cases in which quaternary relations appear in practice, so
; we provide a basic ontology of them as part of our set theoretic ontology.

; Quaternary multirelations
(defn complete-quaternary-relation
  [coll]

  (cartesian-power coll 4))

(defn complete-quaternary-relation?
  [rel]

  (and
    (relation? rel)
    (equal-universals? rel (complete-quaternary-relation (vertices rel)))))

(defn quaternary-multirelation?
  [rel]

  (and
    (multiset? rel)
    (every? size-four-seq? rel)))

(defn equal-quaternary-multirelation?
  [rel]

  (and
    (equal-multiset? rel)
    (every? size-four-seq? rel)))

(def quaternary-relation?
  (power-set size-four-seq?))

(def single-valued-quaternary-relation?
  (intersection
    quaternary-relation?
    (functional-dependency #{0 1 2} #{3})))