(ns locus.linear.associative-algebra.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.semiring.core.object :refer :all]
            [locus.semiring.core.morphism :refer :all]
            [locus.ring.core.object :refer :all]
            [locus.ring.core.protocols :refer :all]))

; Associative algebras
; Let R be a ring, then an associative algebra over R is a ring over R
; that is simultaneously a module over R. In some cases, the underlying
; base ring might be required to be a field, so that the associative
; algebra must necessarily form a field.

(deftype AssociativeAlgebra [elems add mul scalars scale]
  ConcreteObject
  (underlying-set [this] elems)

  EffectSystem
  (actions [this] (underlying-set scalars))
  (action-domain [this elem] elems)
  (apply-action [this action arg] (scale action arg)))

(defmethod additive-semigroup AssociativeAlgebra
  [^AssociativeAlgebra algebra]

  (.add algebra))

(defmethod multiplicative-semigroup AssociativeAlgebra
  [^AssociativeAlgebra algebra]

  (.mul algebra))

(derive AssociativeAlgebra :locus.ring.core.protocols/semiring)

; Convert a ring homomorphism into an associative algebra
(defn ring-homomorphism->algebra
  [hom]

  (let [target-ring (target-object hom)
        source-ring (source-object hom)]
    (AssociativeAlgebra.
      (underlying-set target-ring)
      (additive-semigroup target-ring)
      (multiplicative-semigroup target-ring)
      (underlying-set source-ring)
      (fn [source-element target-element]
        ((multiplicative-semigroup target-ring) [(hom source-element) target-element])))))