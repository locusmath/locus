(ns locus.semimodule.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.monoid.arithmetic :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.morphism :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semiring.core.morphism :refer :all]
            [locus.semimodule.core.utils :refer :all])
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

(derive Semimodule :locus.base.logic.structure.protocols/structured-set)

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

(defmethod to-semimodule :locus.elementary.copresheaf.core.protocols/monoid
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






