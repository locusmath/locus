(ns locus.elementary.function.young-distribution.dist
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.nms :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.clan :refer :all]
            [locus.elementary.incidence.system.ec :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; A young distribution is simply a map from a set to young's lattice. In particular,
; this is useful when dealing with sets of multisets. In that context, each dimember
; of the multiset system can be mapped to its membership signature.
(defn young-distribution
  [coll]

  (let [in (apply union (map set coll))]
    (SetFunction.
      in
      additive-partition?
      (fn [i]
        (membership-signature coll i)))))

; Ontology of young distributions, which are maps from sets to young's lattice
(defn young-distribution?
  [func]

  (and
    (set-function? func)
    (every? additive-partition? (outputs func))))

(def injective-young-distribution?
  (intersection
    young-distribution?
    injective?))

(def constant-young-distribution?
  (intersection
    young-distribution?
    constant-function?))