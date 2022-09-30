(ns locus.elementary.semigroup.monoid.end
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.bijection.core.morphism :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.category.hom.sethom :refer :all]
            [locus.elementary.category.hom.bhom :refer :all]
            [locus.elementary.category.hom.dhom :refer :all]
            [locus.elementary.category.hom.funhom :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.diset.core.object Diset)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.semigroup.monoid.object Monoid)))

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

(defmethod end :locus.base.logic.core.set/universal
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
