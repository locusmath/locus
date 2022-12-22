(ns locus.algebra.commutative.monoid.group-with-zero
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.commutative.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.abelian.group.object :refer :all])
  (:import (locus.algebra.abelian.group.object CommutativeGroup)))

; Let F be a field. Then the multiplicative semigroup (F,*) of the field is a commutative group with
; zero. The importance of commutative groups with zero to us is that it lets us describe the
; multiplicative properties of fields.

(deftype CommutativeGroupWithZero [elems op id inv zero]
  ConcreteObject
  (underlying-set [this] elems)

  ; Semigroups are semigroupoids and so they are structured quivers
  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ; Every semigroup is a function
  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive CommutativeGroupWithZero :locus.set.copresheaf.structure.core.protocols/commutative-group-with-zero)

; Mulmithedos for commutative groups with zero
(defmethod invert-element CommutativeGroupWithZero
  [^CommutativeGroupWithZero group, x]

  ((.inv group) x))

(defmethod identity-elements CommutativeGroupWithZero
  [^CommutativeGroupWithZero group] #{(.id group)})

(defmethod zero-elements CommutativeGroupWithZero
  [^CommutativeGroupWithZero group] #{(.zero group)})

(defmethod group-of-units CommutativeGroupWithZero
  [^CommutativeGroupWithZero group]

  (CommutativeGroup.
    (disj (underlying-set group) (zero-element group))
    (.op group)
    (.id group)
    (.inv group)))

; Every single commutative group with zero has a simple realisation as a
(defmethod natural-preorder CommutativeGroupWithZero
  [^CommutativeGroupWithZero semigroup]

  (let [zero-element (.-zero semigroup)]
    (fn [[a b]]
      (if (= b zero-element)
        true
        (not= a zero-element)))))