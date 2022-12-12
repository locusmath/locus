(ns locus.algebra.semigroup.numerical.numerical-monoid
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.numeric.ap :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; Let (N,+) be the monoid consisting of all natural numbers under addition. Then
; a numerical monoid is simply an additive submonoid of this monoid, in particular
; one that doesn't have a non-trivial greatest common divisor. A numerical monoid
; is stored internally on the machine in terms of a list of generators. The list
; of generators can of course be restored using the morphic-gens function.

(deftype NumericalMonoid [gens]
  ; The underlying set of a numerical monoid can be produced by factorisation
  ConcreteObject
  (underlying-set [this]
    (unrestricted-sumset (set gens)))

  ; Every monoid is a structured quiver
  StructuredDiset
  (first-set [this] (underlying-set this))
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this]
    (singular-quiver (unrestricted-sumset (set gens)) 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this]
    (singular-unital-quiver (unrestricted-sumset (set gens)) 0 0))
  (identity-morphism-of [this obj] 0)

  ; Every monoid is a structured function
  ConcreteMorphism
  (inputs [this] (complete-relation (underlying-set this)))
  (outputs [this] (underlying-set this))

  clojure.lang.IFn
  (invoke [this [a b]] (+ a b))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive NumericalMonoid :locus.set.copresheaf.structure.core.protocols/monoid)

; Restore the morphic generating set of the numerical monoid
(defmethod morphic-gens NumericalMonoid
  [^NumericalMonoid monoid]

  (.gens monoid))

; Convert a numerical monoid back in to an ordinary monoid
(defmethod to-monoid NumericalMonoid
  [^NumericalMonoid monoid]

  (->Monoid
    (underlying-set monoid)
    (fn [[a b]]
      (+ a b))
    0))
