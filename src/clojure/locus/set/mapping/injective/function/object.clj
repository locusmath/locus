(ns locus.set.mapping.injective.function.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all])
  (:import (locus.set.logic.limit.product CartesianCoproduct)))

; An injective function f: A -> B is one for which given any two values a1 and a2 we have that
; f(a1) = f(a2) implies that a1=a2. Injective functions are invertible, except for their
; function images which can be different from B if the function is not surjective.
(deftype InjectiveFunction [in out func]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  ConcreteObject
  (underlying-set [this] (CartesianCoproduct. [in out]))

  clojure.lang.IFn
  (invoke [this obj] (func obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive InjectiveFunction :locus.set.logic.structure.protocols/injective-set-function)

; Injective functions form their own category, which is a subcategory of the topos of sets
(defmethod compose* InjectiveFunction
  [a b]

  (->InjectiveFunction
    (inputs b)
    (outputs a)
    (comp (.func a) (.func b))))

(defn injective-identity-function
  [coll]

  (->InjectiveFunction
    coll
    coll
    identity))