(ns locus.linear.semimodule.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.object :refer :all]
            [locus.semiring.core.object :refer :all]
            [locus.semiring.core.morphism :refer :all]
            [locus.linear.semimodule.utils :refer :all])
  (:import (locus.elementary.group.core.object Group)
           (locus.elementary.action.global.object MSet)))

; A semimodule is like a commutative monoid with operators
(deftype Semimodule
  [ring semigroup scale]

  ConcreteObject
  (underlying-set [this] (underlying-set semigroup))

  EffectSystem
  (actions [this] (underlying-set ring))
  (action-domain [this elem] (underlying-set semigroup))
  (apply-action [this elem arg] (scale elem arg)))

(derive Semimodule :locus.elementary.function.core.protocols/structured-set)

; Functorially map a semimodule to the category of commutative monoids
(defmethod additive-semigroup Semimodule
  [^Semimodule module] (.semigroup module))

; Functorially map a semimodule to the topos of monoid actions
(defmethod to-mset Semimodule
  [^Semimodule semimodule]

  (MSet.
    (multiplicative-semigroup (.ring semimodule))
    (underlying-set semimodule)
    (.scale semimodule)))

; Ontology of semimodules and modules
(derive Semimodule :locus.linear.semimodule.utils/semimodule)

(defmethod module? :locus.linear.semimodule.utils/semimodule
  [semimodule]

  (group? (additive-semigroup semimodule)))

; General conversion routines to convert things into semimodules
(defmulti to-semimodule type)

(defmethod to-semimodule Semimodule
  [semimodule] semimodule)

(defmethod to-semimodule :locus.elementary.function.core.protocols/monoid
  [monoid]

  (Semimodule.
    nn
    monoid
    (fn [n x]
      (iterate-monoid-element monoid x n))))

; Self induced semimodules of semirings
(defn self-induced-semimodule
  [semiring]

  (Semimodule.
    semiring
    (additive-semigroup semiring)
    (fn [a x]
      ((multiplicative-semigroup semiring) [a x]))))

; Compute the subalgebra lattice of a semimodule
(defn subsemimodule?
  [semimodule coll]

  (and
    (identity-preserving-subsemigroup? (.semigroup semimodule) coll)
    (action-closed-set? semimodule coll)))

(defn subsemimodules
  [semimodule]

  (set
    (filter
      (fn [coll]
        (subsemimodule? semimodule coll))
      (power-set (underlying-set semimodule)))))

(defmethod sub Semimodule
  [semimodule]

  (->Lattice
    (subsemimodules semimodule)
    union
    intersection))






