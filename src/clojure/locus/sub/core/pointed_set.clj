(ns locus.sub.core.pointed-set
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.inclusion.object :refer :all]
            [locus.sub.core.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; Pointed sets are functional algebras so they implement IFn
; A pointed set is simply an ordered pair (S,p) of a set S together
; with a point p that is contained in S.
(deftype PointedSet [coll elem]
  ConcreteObject
  (underlying-set [this] coll)

  ConcreteMorphism
  (inputs [this] #{elem})
  (outputs [this] coll)

  clojure.lang.IFn
  (invoke [this arg] arg)
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive PointedSet :locus.sub.core.object/set-subalebra)

; The included elements method makes pointed sets act like subalgebras
(defmethod included-elements PointedSet
  [^PointedSet pointed-set]

  #{(.-elem pointed-set)})

; Convert pointed sets into inclusion functions
(defmethod to-function PointedSet
  [^PointedSet pointed-set]

  (->InclusionFunction (included-elements pointed-set) (underlying-set pointed-set)))

; Conversion routines
(defmulti to-pointed-set type)

(defmethod to-pointed-set PointedSet
  [pointed-set] pointed-set)

(defmethod to-pointed-set SetFunction
  [func]

  (let [input-element (first (inputs func))
        output-element (func input-element)]
    (PointedSet. (outputs func) output-element)))

; Products in the category of pointed sets
(defmethod product PointedSet
  [& pointed-sets]

  (PointedSet.
    (apply cartesian-product pointed-sets)
    (map #(.elem %) pointed-sets)))

; Restrictions of pointed sets
(defn restrict-pointed-set
  [pointed-set coll]

  (PointedSet.
    coll
    (.elem pointed-set)))

