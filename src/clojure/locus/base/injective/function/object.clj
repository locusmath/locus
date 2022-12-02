(ns locus.base.injective.function.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.sequence.core.object :refer :all]))

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

(derive InjectiveFunction :locus.base.logic.structure.protocols/injective-set-function)

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