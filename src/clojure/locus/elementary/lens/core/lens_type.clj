(ns locus.elementary.lens.core.lens-type
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]))

; Abstracting away the idea of the getter and setter of a lens and its representation
; related aspects, to describe only the basic idea of a memory location. We will store
; active and stable as equivalence relations.
(deftype LensType [coll active stable]
  ConcreteObject
  (underlying-set [this]
    coll))

; Every lens type is associated with a dual which can be defined by
; swapping the active and the stable parts of the lens.
(defn dual-lens-type
  [^LensType lens]

  (LensType.
    (.coll lens)
    (.stable lens)
    (.active lens)))

