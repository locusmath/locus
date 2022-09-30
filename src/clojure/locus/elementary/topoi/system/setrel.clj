(ns locus.elementary.topoi.system.setrel
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]))

; Binary relation on sets
; These are generalisations of functional dependency relations. Furthermore,
; they can be considered to be object systems in the topos of pairs of sets.
(defn binary-relation-on-sets?
  [coll]

  (and
    (universal? coll)
    (every?
      (fn [i]
        (and
          (size-two-seq? i)
          (every? universal? i)))
      coll)))

; Implementation of armstrongs axioms
; Augmentation is basically the same as union closure and reflexivity
; is the same as restriction closure
(def transitive-binary-relation-on-sets?
  (intersection
    transitive?
    binary-relation-on-sets?))

(def reflexive-relation-on-sets?
  (intersection
    reflexive?
    binary-relation-on-sets?))

(def preorder-on-sets?
  (intersection
    preorder?
    binary-relation-on-sets?))

(defn union-closed-binary-relation-on-sets?
  [rel]

  (and
    (binary-relation-on-sets? rel)
    (and
      (every?
        (fn [[[a b] [c d]]]
          (rel (list (union a c) (union b d))))
        (cartesian-power rel 2)))))

(def restriction-closed-binary-relation-on-sets?
  (moore-family
    (intersection size-two-seq? (partial every? universal?))
    (fn [coll]
      (let [ground-sets (power-set (apply union (vertices coll)))]
        (union
          coll
          (set
           (mapcat
             (fn [ground-set]
               (map
                 (fn [subset]
                   (list ground-set subset))
                 (power-set ground-set)))
             ground-sets)))))))

(def armstrong-relation?
  (intersection
    transitive-binary-relation-on-sets?
    union-closed-binary-relation-on-sets?
    restriction-closed-binary-relation-on-sets?))

(defn nary-functional-dependencies
  [rel n]

  (set
    (filter
      (fn [[source-slots target-slots]]
        (satisfies-functional-dependency? rel source-slots target-slots))
      (cartesian-power (power-set (set (range n))) 2))))

(defn binary-functional-dependencies
  [rel]

  (nary-functional-dependencies rel 2))

(defn nary-singleton-functional-dependencies
  [rel n]

  (set
    (filter
      (fn [[source-slot target-slot]]
        (satisfies-functional-dependency? rel #{source-slot} #{target-slot}))
      (cartesian-power (set (range n)) 2))))

; Special methods for dealing with particular classes of set relations
(def singletons-relation?
  (power-set
    (fn [[a b]]
      (and
        (singular-universal? a)
        (singular-universal? b)))))

(defn singletonize-relation
  [rel]

  (set (map (fn [[a b]] (list #{a} #{b})) rel)))