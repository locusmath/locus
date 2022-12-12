(ns locus.order.lattice.total.open-set
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.total.object :refer :all]
            [locus.order.lattice.total.open-interval :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.total.object TotallyOrderedSet)))

; The base of the order topology of a finite total order consists of open intervals,
; open rays, and the entire set X. Then given these generators we can form any
; open set from a union of them. This total order open set class is designed to handle
; the data of these unions. With this we construct the order topology of a total order.
(deftype TotalOrderOpenSet [order components]
  clojure.lang.IFn
  (invoke [this arg]
    (and
      ((underlying-set order) arg)
      (every?
        (fn [component]
          (component arg))
        components)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defmethod union* TotalOrderOpenSet
  [^TotalOrderOpenSet a, ^TotalOrderOpenSet b]

  (TotalOrderOpenSet. (.order a) (union (.components a) (.components b))))

(defn open-set-of-total-order?
  [order open]

  (and
    (= (type open) TotalOrderOpenSet)
    (= (.space open) order)))
