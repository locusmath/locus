(ns locus.elementary.category.relational.functor
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.relational.relation.set-relation :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.partial.object :refer :all])
  (:import (locus.elementary.semigroup.partial.object PartialTransformationSemigroup)))

; A relation functor is a morphism of the following form:
; F: C -> Rel
; Such a functor is sort of like a multivalued copresheaf.

; This is the main wrapper we will use to create relational functors
(defn relational-functor
  [category object-function arrow-function]

  (->Functor
    category
    set-relations
    arrow-function
    object-function))

(defn copresheaf->relational-functor
  [copresheaf]

  (relational-functor
    (source-object copresheaf)
    (fn [obj]
      (object-apply copresheaf obj))
    (fn [arrow]
      (to-set-relation (morphism-apply copresheaf arrow)))))

(defn set-relation->relational-functor
  [rel]

  (relational-functor
    (n-arrow-category 1)
    (fn [object]
      0 (source-object rel)
      1 (target-object rel))
    (fn [arrow]
      (case arrow
        0 (identity-relation (source-object rel))
        1 (identity-relation (target-object rel))
        2 rel))))

(defn binary-relation-on-sets->relational-functor
  [coll]

  (let [sorted-coll (seq coll)
        source (set (range (count sorted-coll)))
        target (apply union (map (partial apply union) coll))]
    (relational-functor
      (n-arrow-category 2)
      (fn [object]
        (case object
          0 source
          1 target))
      (fn [arrow]
        (case arrow
          0 (identity-relation source)
          1 (identity-relation target)
          2 (->SetRelation
              source
              target
              (fn [i]
                (first (nth sorted-coll i))))
          3 (->SetRelation
              source
              target
              (fn [i]
                (second (nth sorted-coll i)))))))))

(defn partial-transformation-semigroup->relational-functor
  [^PartialTransformationSemigroup transformation-semigroup]

  (when (intrinsic-monoid? (.semigroup transformation-semigroup))
    (relational-functor
      (.semigroup transformation-semigroup)
      (fn [object]
        (case object
          0 (.coll transformation-semigroup)))
      (fn [arrow]
        (morphism-to-relation transformation-semigroup arrow)))))