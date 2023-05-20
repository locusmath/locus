(ns locus.set.mapping.general.core.preorder
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.sub.mapping.function :refer :all]
            [locus.set.mapping.function.core.functor :refer :all]
            [locus.partial.mapping.function :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer [coreflexive-relation complete-relation]]
            [locus.order.lattice.core.object :refer :all])
  (:import (locus.set.quiver.unary.core.morphism Diamond)))

; preorders section
; get all preorders on a set
(defn set-preorders
  [coll]

  (set
    (map
      set
      (filter
        preorder?
        (logical-interval
          (coreflexive-relation coll)
          (complete-relation coll))))))

(defn preorder-inverse-image
  [func preorder]

  (set
    (filter
      (fn [[a b]]
        (preorder (list (func a) (func b))))
      (cartesian-power (inputs func) 2))))

; logical properties of preorder pairs
(defn preorder-pairs
  [func]

  (let [input-preorders (set-preorders (set (inputs func)))
        output-preorders (set-preorders (set (outputs func)))]
    (set
      (mapcat
        (fn [out-preorder]
          (let [maximum-input-preorder (preorder-inverse-image func out-preorder)]
            (for [input-preorder input-preorders
                  :when (superset? (list (set input-preorder) maximum-input-preorder))]
              (list input-preorder out-preorder))))
        output-preorders))))

(defn preorder-pairs-ordering
  [func]

  (let [pairs (preorder-pairs func)]
    (set
      (filter
        (fn [[[a b] [c d]]]
          (and
            (superset? (list a c))
            (superset? (list b d))))
        (cartesian-product pairs pairs)))))
