(ns locus.grothendieck.topology.core.continuous-real-valued-function
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.elementary.logic.base.core :refer :all :exclude [add]]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.grothendieck.topology.core.object :refer :all]
            [locus.grothendieck.topology.core.morphism :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.arithmetic :refer :all]
            [locus.ring.core.object :refer :all]
            [locus.ring.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.group-with-zero :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all])
  (:import (locus.grothendieck.topology.core.object TopologicalSpace)))

; The sections of the sheaf of rings of continuous real valued functions on a topological space
; Let X be a topological space with a set of opens Op(X), then X we can define a sheaf
; of rings on X by the sheaf mapping each open set O to the ring of real valued continuous
; mappings on O. Each restriction morphism in the base site is then mapped to a restriction
; homomorphism of sheafs of continuous real valued functions.

(deftype ContinuousRealValuedFunction [in func]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] real-number?)

  ConcreteMorphism
  (inputs [this] (source-object this))
  (outputs [this] (target-object this))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Arithmetic
(defmethod negate ContinuousRealValuedFunction
  [^ContinuousRealValuedFunction func]

  (ContinuousRealValuedFunction.
    (.in func)
    (fn [n]
      (- (func n)))))

(defmethod add [ContinuousRealValuedFunction ContinuousRealValuedFunction]
  [^ContinuousRealValuedFunction a, ^ContinuousRealValuedFunction b]

  (ContinuousRealValuedFunction.
    (.in a)
    (fn [n]
      (+ (a n) (b n)))))

(defmethod multiply [ContinuousRealValuedFunction ContinuousRealValuedFunction]
  [^ContinuousRealValuedFunction a, ^ContinuousRealValuedFunction b]

  (ContinuousRealValuedFunction.
    (.in a)
    (fn [n]
      (* (a n) (b n)))))

(defn zero-continuous-real-valued-function
  [coll]

  (ContinuousRealValuedFunction.
    coll
    (fn [n]
      0)))

(defn ring-of-continuous-real-valued-functions
  [coll]

  (let [elem? (fn [x]
                (and
                  (= (type x) ContinuousRealValuedFunction)
                  (= (source-object x) coll)))]
    (make-ring
      (Group.
        elem?
        (fn [[a b]]
          (+ a b))
        (zero-continuous-real-valued-function coll)
        (fn [a]
          (- a)))
      (Semigroup.
        elem?
        (fn [[a b]]
          (* a b))))))

(defn restrict-continuous-real-valued-function
  [func coll]

  (ContinuousRealValuedFunction.
    coll
    (fn [i]
      (func i))))

(defn continuous-real-valued-function-ring-restriction-homomorphism
  [old-coll new-coll]

  (->RingMorphism
    (ring-of-continuous-real-valued-functions old-coll)
    (ring-of-continuous-real-valued-functions new-coll)
    (fn [func]
      (restrict-continuous-real-valued-function func new-coll))))

