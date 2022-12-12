(ns locus.sub.core.pointed-set
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.function.inclusion.object :refer :all]
            [locus.sub.core.object :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; Pointed sets are functional algebras, so they implement IFn
; A pointed set is simply an ordered pair (S,p) of a set S together
; with a point p that is contained in S. Pointed sets are also like
; subsets of a set which only contain a single element, so they can be
; dealt with as part of our subalgebras framework.
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

; Convert pointed sets back in to set subalgebras
(defmethod to-set-subalgebra PointedSet
  [^PointedSet pointed-set]

  (set-subalgebra (included-elements pointed-set) (underlying-set pointed-set)))

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

