(ns locus.elementary.category.system.object-system
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.element.object :refer :all])
  (:import (locus.elementary.category.element.object CategoryObject)))

; Let C be a category, and Ob(C) its set of objects. Then the power set P(Ob(C))
; is the set of object systems of C. We see object systems for example, in
; the theory of ideals and filters of lattices.

(def object-system?
  (power-set
    (fn [i]
      (= (type i) CategoryObject))))

(def singular-object-system?
  (intersection
    singular-universal?
    object-system?))

(def size-two-object-system?
  (intersection
    size-two-universal?
    object-system?))

(def size-three-object-system?
  (intersection
    size-three-universal?
    object-system?))

(def size-four-object-system?
  (intersection
    size-four-universal?
    object-system?))