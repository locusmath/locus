(ns locus.set.mapping.function.core.functor
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Functors from the topos Sets to other categories
; We can start by making set and partition images into functors
(defn image-functor
  [func]

  (SetFunction.
    (->PowerSet (inputs func))
    (->PowerSet (outputs func))
    (fn [coll]
      (set-image func coll))))

(defn inverse-image-functor
  [func]

  (SetFunction.
    (->PowerSet (outputs func))
    (->PowerSet (inputs func))
    (fn [coll]
      (set-inverse-image func coll))))

(defn partition-image-functor
  [func]

  (SetFunction.
    (->BellSet (inputs func))
    (->BellSet (outputs func))
    (fn [partition]
      (partition-image func partition))))

(defn partition-inverse-image-functor
  [func]

  (SetFunction.
    (->BellSet (outputs func))
    (->BellSet (inputs func))
    (fn [partition]
      (partition-inverse-image func partition))))

; This is a functor that takes values in tuples
(defn tuples-functor
  [func n]

  (SetFunction.
    (cartesian-power (inputs func) n)
    (cartesian-power (outputs func) n)
    (partial map func)))

(defn families-functor
  [func]

  (SetFunction.
    (->PowerSet (->PowerSet (inputs func)))
    (->PowerSet (->PowerSet (outputs func)))
    (fn [family]
      (set
        (map
          (fn [i]
            (set-image func i))
          family)))))
