(ns locus.cmon.action.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.action.core.protocols :refer :all]
            [locus.set.action.global.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]))

; A commutative monoid with operators is a commutative monoid M with the action of some other
; monoid which is not necessarily commutative acting on it.
(deftype CommutativeMonoidWithOperators [source semigroup scale]
  ConcreteObject
  (underlying-set [this] (underlying-set source))

  EffectSystem
  (actions [this] (underlying-set source))
  (action-domain [this elem] (underlying-set semigroup))
  (apply-action [this action elem] (scale action elem)))

(derive CommutativeMonoidWithOperators :locus.set.logic.structure.protocols/structured-set)

; Adding commutative monoids with operators into the structure copresheaf framework
(defmethod index CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid] (.-source monoid))

(defmethod get-object CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid, x]

  (.-semigroup monoid))

(defmethod get-morphism CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid, action]

  (monoid-endomorphism
    (.-semigroup monoid)
    (fn [x]
      (apply-action monoid action x))))

(defmethod get-set CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid, x] (underlying-set (get-object monoid x)))

(defmethod get-function CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid, action] (underlying-function (get-morphism monoid action)))

; Additive semigroups for commutative monoids with operators
(defmethod additive-semigroup CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid] (.-semigroup monoid))

; Conversion routines
(defmethod to-mset CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid]

  (->MSet
    (.-source monoid)
    (underlying-set monoid)
    (.-scale monoid)))

(defmulti to-commutative-monoid-with-operators type)

(defmethod to-commutative-monoid-with-operators CommutativeMonoidWithOperators
  [^CommutativeMonoidWithOperators monoid] monoid)

; Ontology of commutative monoids with operators
(defn commutative-monoid-with-operators?
  [monoid]

  (= (type monoid) CommutativeMonoidWithOperators))
