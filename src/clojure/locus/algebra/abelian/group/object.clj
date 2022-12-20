(ns locus.algebra.abelian.group.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.copresheaf.quiver.dependency.object :refer :all]
            [locus.con.core.object :refer [projection]]
            [locus.con.core.setpart :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.commutative.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all])
  (:import (locus.algebra.commutative.semigroup.object CommutativeSemigroup)))

; Commutative groups are Z-modules. Once all relevant module related libraries have been loaded
; abelian groups can be converted into Z-modules by using the to-module command.

(deftype CommutativeGroup [elems op id inv]
  ConcreteObject
  (underlying-set [this] elems)

  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  StructuredUnitalQuiver
  (underlying-unital-quiver [this] (singular-unital-quiver elems 0 id))
  (identity-morphism-of [this obj] id)

  StructuredPermutableQuiver
  (invert-morphism [this x] (inv x))
  (underlying-permutable-quiver [this] (singular-permutable-quiver elems 0 inv))

  StructuredDependencyQuiver
  (underlying-dependency-quiver [this] (singular-dependency-quiver elems 0 id inv))

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (op obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive CommutativeGroup :locus.set.copresheaf.structure.core.protocols/commutative-group)

; Identity and inverse elements
(defmethod invert-element CommutativeGroup
  [^CommutativeGroup group, x] ((.inv group) x))

(defmethod identity-elements CommutativeGroup
  [^CommutativeGroup group] #{(.id group)})

; The natural preorder on a commutative group is trivial and its condensation is the trivial monoid
(defmethod natural-preorder CommutativeGroup
  [^CommutativeGroup group] (fn [[a b]] true))

(defmethod natural-condensation CommutativeGroup
  [^CommutativeGroup group]  trivial-monoid)

(defmethod to-commutative-monoid CommutativeGroup
  [^CommutativeGroup group]

  (->CommutativeMonoid
    (.-elems group)
    (fn [[a b]]
      true)
    (.-op group)
    (.-id group)))

; Products of objects in the concrete category Ab of abelian groups
(defmethod product CommutativeGroup
  [& groups]

  (CommutativeGroup
    (apply cartesian-product (map underlying-set groups))
    (apply semigroup-product-function groups)
    (map identity-element groups)
    (fn [obj]
      (map-indexed
        (fn [i v]
          ((.inv (nth groups i)) v))
        obj))))

; Convert other objects into commutative groups whenever possible
(defmulti to-commutative-group type)

(defmethod to-commutative-group CommutativeGroup
  [^CommutativeGroup group] group)

; The group of units of a commutative group is the entire group itself
(defmethod group-of-units CommutativeGroup
  [^CommutativeGroup group] group)


