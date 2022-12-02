(ns locus.module.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.semimodule.core.utils :refer :all])
  (:import (locus.elementary.action.global.object MSet)))

; A module is like a group with operators
(deftype Module
  [ring semigroup scale]

  ConcreteObject
  (underlying-set [this] (underlying-set semigroup))

  EffectSystem
  (actions [this] (underlying-set ring))
  (action-domain [this elem] (underlying-set semigroup))
  (apply-action [this elem arg] (scale elem arg)))

(derive Module :locus.base.logic.structure.protocols/structured-set)

(defmethod additive-semigroup Module
  [^Module module] (.semigroup module))

(defmethod to-mset Module
  [^Module module]

  (MSet.
    (multiplicative-semigroup (.ring module))
    (underlying-set module)
    (.scale module)))

; Ontology of modules
(derive Module :locus.semimodule.core.utils/module)

; Conversion of objects to modules
(defmulti to-module type)

(defmethod to-module Module
  [module] module)

(defmethod to-module :locus.elementary.copresheaf.core.protocols/group
  [group]

  (Module.
    zz
    group
    (fn [n x]
      (iterate-group-element group x n))))

; Self induced modules of rings
(defn self-induced-module
  [ring]

  (Module.
    ring
    (additive-semigroup ring)
    (fn [a x]
      ((multiplicative-semigroup ring) (list a x)))))

; Lattices of submodules
; This is more efficient because it can make use of Lagrange's theorem
(defn submodule?
  [module coll]

  (and
    (subgroup? (.semigroup module) coll)
    (action-closed-set? module coll)))

(defn submodules
  [module]

  (set
    (filter
      (fn [coll]
        (action-closed-set? module coll))
      (all-subgroups (.semigroup module)))))

(defmethod sub Module
  [module]

  (->Lattice
    (submodules module)
    union
    intersection))

; Classify rings by their modules
(defn module-ring-classifier
  [ring]

  (->Universal
    (fn [module]
      (and
        (= (type module) Module)
        (= (.ring module) ring)))))

; Ontology of modules
(defn module?
  [module]

  (= (type module) Module))

