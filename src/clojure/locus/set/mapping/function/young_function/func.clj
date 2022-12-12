(ns locus.set.mapping.function.young-function.func
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.numeric.nms :refer :all]
            [locus.set.logic.numeric.sig :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.numeric.nr :refer :all]))

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