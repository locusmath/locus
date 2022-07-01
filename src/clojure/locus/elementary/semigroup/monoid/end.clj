(ns locus.elementary.semigroup.monoid.end
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.gem.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.hom.functional.sethom :refer :all]
            [locus.elementary.hom.functional.bhom :refer :all]
            [locus.elementary.hom.functional.dhom :refer :all]
            [locus.elementary.hom.functional.funhom :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)
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

(defmethod end :default
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
