(ns locus.elementary.category.object.category-object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]))

; Let C be a category, then Ob(C) denotes its set of objects.
; In this file, we provide a runtime class that defines objects of C.

(deftype CategoryObject [category object])

(defn category-objects
  [category]

  (set
    (map
      (fn [object]
        (CategoryObject. category object))
      (objects category))))

(defn category-object?
  [x]

  (= (type x) CategoryObject))

