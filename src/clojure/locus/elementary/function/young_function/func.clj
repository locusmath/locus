(ns locus.elementary.function.young-function.func
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.nms :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.logic.base.sig :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.relation.numeric.nr :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

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