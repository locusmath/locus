(ns locus.base.function.young-distribution.dist
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.numeric.nms :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.clan :refer :all]
            [locus.elementary.incidence.system.ec :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

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