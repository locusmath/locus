(ns locus.algebra.semigroup.monoid.end
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.copresheaf.bijection.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.category.hom.sethom :refer :all]
            [locus.algebra.category.hom.bhom :refer :all]
            [locus.algebra.category.hom.dhom :refer :all]
            [locus.algebra.category.hom.funhom :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)
           (locus.set.quiver.diset.core.object Diset)
           (locus.set.copresheaf.bijection.core.object Bijection)
           (locus.algebra.semigroup.monoid.object Monoid)))

; Let C be a category, and let X be an element of Ob(C). Then Hom(X,X) is the hom class of all
; morphisms from X to X, which is also the endomorphism monoid of X. It follows that endomorphisms
; are constructed as part of a larger effort to define generic hom classes for objects of
; categories. The special functionality for constructing hom classes is defined in the hom folder.
; Once we can construct hom classes then we can define endomorphism monoids in the standard fashion.

; Get the endomorphism monoid of a set
(defn set-endomorphism-monoid
  [coll]

  (Monoid.
    (set-hom coll coll)
    (fn [[f g]]
      (compose f g))
    (identity-function coll)))

; Endomorphism monoids
(defmulti end type)

(defmethod end :locus.set.logic.core.set/universal
  [coll]

  (set-endomorphism-monoid coll))

(defmethod end SetFunction
  [func]

  (Monoid.
    (function-morphisms func func)
    (fn [[f g]]
      (compose f g))
    (identity-morphism func)))

(defmethod end Diset
  [coll]

  (Monoid.
    (diset-hom coll coll)
    (fn [[f g]]
      (compose f g))
    (identity-morphism coll)))

(defmethod end Bijection
  [func]

  (Monoid.
    (bijection-hom func func)
    (fn [[f g]]
      (compose f g))
    (identity-morphism func)))
