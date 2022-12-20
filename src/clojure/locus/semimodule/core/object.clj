(ns locus.semimodule.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.action.core.protocols :refer :all]
            [locus.set.action.global.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.morphism :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semiring.core.morphism :refer :all]
            [locus.semimodule.core.utils :refer :all])
  (:import (locus.algebra.group.core.object Group)
           (locus.set.action.global.object MSet)))

; A semimodule is like a commutative monoid with operators
(deftype Semimodule
  [ring semigroup scale]

  ConcreteObject
  (underlying-set [this] (underlying-set semigroup))

  EffectSystem
  (actions [this] (underlying-set ring))
  (action-domain [this elem] (underlying-set semigroup))
  (apply-action [this elem arg] (scale elem arg)))

(derive Semimodule :locus.set.logic.structure.protocols/structured-set)

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
(derive Semimodule :locus.semimodule.core.utils/semimodule)

(defmethod module? :locus.semimodule.core.utils/semimodule
  [semimodule]

  (group? (additive-semigroup semimodule)))

; General conversion routines to convert things into semimodules
(defmulti to-semimodule type)

(defmethod to-semimodule Semimodule
  [semimodule] semimodule)

(defmethod to-semimodule :locus.set.copresheaf.structure.core.protocols/monoid
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






