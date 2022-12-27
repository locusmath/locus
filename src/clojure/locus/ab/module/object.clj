(ns locus.ab.module.object
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
            [locus.algebra.group.core.morphism :refer :all])
  (:import (locus.set.action.global.object MSet)))

; Let Ab the category of abelian groups with functors between them. Then Ab is a concrete cartesian
; monoidal category. As a concrete cartesian monoidal category, it is possible to form enriched
; copresheaves over it. This theory has two aspects (1) the formation of Ab-enriched categories
; which are essentially the horizontal categorification of rings and (2) the theory of copresheaves
; of abelian groups. Then by combining these two we can get Ab-enriched copresheaves of abelian
; groups of which modules are an example. In particular, we define a module to be a presheaf
; of abelian groups over a ring.

(deftype Module
  [ring semigroup scale]

  ConcreteObject
  (underlying-set [this] (underlying-set semigroup))

  EffectSystem
  (actions [this] (underlying-set ring))
  (action-domain [this elem] (underlying-set semigroup))
  (apply-action [this elem arg] (scale elem arg)))

(derive Module :locus.set.logic.structure.protocols/structured-set)

; Modules as structure copresheaves
(defmethod index Module
  [^Module module] (.-ring module))

(defmethod get-object Module
  [^Module module, x] (.-semigroup module))

(defmethod get-morphism Module
  [^Module module, action]

  (group-endomorphism
    (.-semigroup module)
    (fn [x]
      (apply-action module action x))))

(defmethod get-set Module
  [^Module module, x] (morphisms (get-object module x)))

(defmethod get-function Module
  [^Module module, x] (underlying-function (get-morphism module x)))

; Modules have a single underlying group object associated to them
(defmethod additive-semigroup Module
  [^Module module] (.semigroup module))

; Convert modules into various objects
(defmethod to-mset Module
  [^Module module]

  (MSet.
    (multiplicative-semigroup (.ring module))
    (underlying-set module)
    (.scale module)))

; Convert various objects into modules
(defmulti to-module type)

(defmethod to-module Module
  [^Module module] module)

(defmethod to-module :locus.set.copresheaf.structure.core.protocols/group
  [group]

  (Module.
    zz
    group
    (fn [n x]
      (iterate-group-element group x n))))

; Self-induced modules of rings
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
