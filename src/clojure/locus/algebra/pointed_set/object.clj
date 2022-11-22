(ns locus.algebra.pointed-set.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.order.lattice.core.object :refer :all])
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

(derive PointedSet :locus.base.logic.structure.protocols/structured-set)

; Conversion
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

; Subalgebra lattice of pointed sets
(defmethod sub PointedSet
  [pointed-set]

  (->Lattice
    (logical-interval #{(.elem pointed-set)} (underlying-set pointed-set))
    union
    intersection))

(defn restrict-pointed-set
  [pointed-set coll]

  (PointedSet.
    coll
    (.elem pointed-set)))

; Congruence lattices of pointed sets
(defmethod con PointedSet
  [pointed-set] (con (underlying-set pointed-set)))

