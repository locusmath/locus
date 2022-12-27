(ns locus.ab.action.object
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
            [locus.algebra.group.core.morphism :refer :all]
            [locus.algebra.abelian.group.object :refer :all]))

; An abelian group with operators is an abelian copresheaf of a monoid F: M -> Ab. So they are
; one of the most basic types of abelian copresheaves. An important point is that, for any
; given module it there is an underlying abelian group with operators.
(deftype AbelianGroupWithOperators [monoid group scale]
  ConcreteObject
  (underlying-set [this] (underlying-set group))

  EffectSystem
  (actions [this] (underlying-set monoid))
  (action-domain [this elem] (underlying-set group))
  (apply-action [this action arg] (scale action arg)))

(derive AbelianGroupWithOperators :locus.set.logic.structure.protocols/structured-set)

; Methods for treating abelian groups with operators as structure copresheaves
(defmethod index AbelianGroupWithOperators
  [^AbelianGroupWithOperators group] (.-monoid group))

(defmethod get-object AbelianGroupWithOperators
  [^AbelianGroupWithOperators group, x]

  (.-group group))

(defmethod get-morphism AbelianGroupWithOperators
  [^AbelianGroupWithOperators group, action]

  (group-endomorphism
    (.-group group)
    (fn [x]
      (apply-action group action x))))

(defmethod get-set AbelianGroupWithOperators
  [^AbelianGroupWithOperators group, x] (morphisms (get-object group x)))

(defmethod get-function AbelianGroupWithOperators
  [^AbelianGroupWithOperators group, action] (underlying-function (get-morphism group action)))

; Abelian groups with operators have an underlying group object
(defmethod additive-semigroup AbelianGroupWithOperators
  [^AbelianGroupWithOperators group]

  (.-group group))

; Abelian groups with operators are structure copresheaves, so they have underlying presheaves
(defmethod to-mset AbelianGroupWithOperators
  [^AbelianGroupWithOperators group]

  (->MSet
    (.-monoid group)
    (underlying-set group)
    (.-scale group)))

; Generalized conversion routines for abelian groups with operators
(defmulti to-abelian-group-with-operators type)

(defmethod to-abelian-group-with-operators AbelianGroupWithOperators
  [^AbelianGroupWithOperators group] group)

; An abelian group with trivial operators is one that has as its index category the terminal
; category consisting of only one object and one morphism.
(defn abelian-group-with-trivial-operators
  [group]

  (->AbelianGroupWithOperators
    trivial-monoid
    group
    (fn [action x]
      x)))

; Ontology of abelian groups with operators
(defn abelian-group-with-operators?
  [obj]

  (= (type obj) AbelianGroupWithOperators))
