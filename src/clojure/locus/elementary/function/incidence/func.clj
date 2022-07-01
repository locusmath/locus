(ns locus.elementary.function.incidence.func
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)))

; Incidence functions can be defined as special set valued functions
; In particular they are set functions that are distinguished by the
; fact that their output set is a power set. The power set class should
; be used to distinguish incidence functions from other set functions.
(defn make-incidence-function
  [source target func]

  (SetFunction.
    source
    (->PowerSet target)
    func))

(defn incidence-function-from-relation
  [rel]

  (make-incidence-function
    (relation-domain rel)
    (vertices rel)
    (fn [i]
      (direct-successors rel i))))

; Properties of incidence functions
(defn incidence-function-flags
  [func]

  (apply
    union
    (map
      (fn [i]
        (set
          (map
            (fn [j]
              (list i j))
            (func i))))
      (inputs func))))

(defn incidence-function-lines
  [func]

  (dimembers (outputs func)))

(defn embedded-incidence-flags
  [func]

  (let [in (inputs func)
        out (incidence-function-lines func)
        rel (->SeqableRelation
              (union in out)
              (fn [[a b]]
                ((func a) b))
              {})]
    (embedded-relation rel in out)))

; Compute duals of incidence functions
(defn dual-incidence-function
  [func]

  (let [in (inputs func)
        out (incidence-function-lines func)]
    (make-incidence-function
      out
      in
      (fn [line]
        (set
          (filter
            (fn [point]
              (contains? (func point) line))
            in))))))

; Ontology of incidence functions
(defn incidence-function?
  [func]

  (and
    (set-function? func)
    (power-set? (outputs func))))

(defn unary-incidence-function?
  [func]

  (and
    (incidence-function? func)
    (every? singular-universal? (incidence-function-lines func))))

(defn binary-incidence-function?
  [func]

  (and
    (incidence-function? func)
    (every? size-two-universal? (incidence-function-lines func))))