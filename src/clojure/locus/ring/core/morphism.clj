(ns locus.ring.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.object :refer :all]))

; Morphisms in the category of rings
; A ring homomorphism f : R -> S is a function of the underlying sets of the rings
; R and S that preserves addition, subtraction, multiplication, and the zero of
; the two rings.
(deftype RingMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Get the morphism of additive groups as a group homomorphism from the forgetful
; functor from the category of rings to the category of abelian groups
(defn morphism-of-additive-groups
  [^RingMorphism ring-homomorphism]

  (->GroupMorphism
    (additive-semigroup (.source ring-homomorphism))
    (additive-semigroup (.target ring-homomorphism))
    (.func ring-homomorphism)))

; Identity morphisms
(defmethod identity-morphism Ring
  [ring]

  (RingMorphism. ring ring identity))

(defmethod compose* RingMorphism
  [a b]

  (RingMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))