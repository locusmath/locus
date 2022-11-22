(ns locus.order.lattice.combinat.ordering
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all])
  (:import (locus.order.lattice.core.object Lattice)))

; Lattices of preorders:
; Let S be a set then Ord(S) is its lattice of preorders. Any two pair of preorders on the
; same set can be joined or meeted to produce another preorder. Furthermore, given any
; preorder it has a lattice of subpreorders, which is the principal down set of the
; preorder in the lattice of preorders. Additionally, this same construction has been
; generalized to produce a lattice of preorders on a function, which is actually a lattice
; of monotone maps.

(defn ^{:private true} distinct-composition-closed-set?
  [rel]

  (every?
    (fn [[[a b] [c d]]]
      (if (and (= b c) (not= a d))
        (boolean (rel (list a d)))
        true))
    (cartesian-power rel 2)))

(defn enumerate-wide-subpreorders
  [coll rel]

  (let [loops (coreflexive-relation coll)
        irreflexive-component-of-rel (set
                                       (filter
                                         (fn [[a b]]
                                           (not= a b))
                                         rel))]
    (set
      (for [rel (power-set irreflexive-component-of-rel)
            :when (distinct-composition-closed-set? rel)]
        (set (union rel loops))))))

(defn enumerate-preorders
  [coll]

  (enumerate-wide-subpreorders coll (complete-relation coll)))

(defn join-preordering-relations
  [& relations]

  (cl transitive? (apply union relations)))

(defn lattice-of-subpreorders
  [rel]

  (Lattice.
    (enumerate-wide-subpreorders (vertices rel) rel)
    join-preordering-relations
    intersection))

(defn lattice-of-preorders
  [coll]

  (Lattice.
    (enumerate-preorders coll)
    join-preordering-relations
    intersection))

(defn enumerate-monotone-pairs
  [func]

  (let [in (inputs func)
        out (outputs func)
        in-preorders (enumerate-preorders in)
        out-preorders (enumerate-preorders out)]
    (set
      (mapcat
        (fn [in-preorder]
          (let [img (set (map (partial map func) in-preorder))]
            (for [out-preorder out-preorders
                 :when (clojure.set/subset? img out-preorder)]
             (list in-preorder out-preorder))))
        in-preorders))))

(defn monotone-pairs-relation
  [func]

  (->SeqableRelation
    (enumerate-monotone-pairs func)
    (fn [[[a b] [c d]]]
      (and
        (superset? (list a c))
        (superset? (list b d))))
    {}))

; Get the lattice of monotone maps of a function
(defn lattice-of-monotone-maps
  [func]
  {:pre (set-function? func)}

  (Lattice.
    (fn [i]
      (and
        (set-function? i)
        (equal-functions? (underlying-function i) func)))
    join-monotone-maps
    meet-monotone-maps))