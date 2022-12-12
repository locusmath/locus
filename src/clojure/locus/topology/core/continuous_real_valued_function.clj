(ns locus.topology.core.continuous-real-valued-function
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.topology.core.object :refer :all]
            [locus.topology.core.morphism :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.ring.core.morphism :refer :all]
            [locus.algebra.semigroup.monoid.arithmetic :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.group-with-zero :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all])
  (:import (locus.topology.core.object TopologicalSpace)))

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

