(ns locus.algebra.category.system.object-system
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.element.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.category.element.object CategoryObject)))

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