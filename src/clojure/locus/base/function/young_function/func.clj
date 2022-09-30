(ns locus.base.function.young-function.func
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.numeric.nms :refer :all]
            [locus.base.logic.numeric.sig :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.relation.numeric.nr :refer :all]))

; Young functions defined in terms of young coordinate systems, which
; in turn can be used to define young's lattice
(defn young-function?
  [func]

  (and
    (set-function? func)
    (young-coordinate-system? (inputs func))))

; Young tableau can now be defined as special types of young functions
; so they are defined by a certain hierarchy of function concepts.
(defn young-tableau?
  [func]

  (and
    (young-function? func)
    (positive-natural-range? (outputs func))))