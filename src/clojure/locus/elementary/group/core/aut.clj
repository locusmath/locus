(ns locus.elementary.group.core.aut
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.util :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.gem.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.hom.functional.funhom :refer :all]
            [locus.elementary.hom.functional.dhom :refer :all]
            [locus.elementary.hom.functional.sethom :refer :all]
            [locus.elementary.hom.functional.bhom :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all])
  (:import (locus.elementary.function.core.object SetFunction)
           (locus.elementary.diset.core.object Diset)
           (locus.elementary.bijection.core.object Bijection)))

; Let C be a category, then the set of all isomorphisms of C forms a wide subcategory called
; the underlying groupoid of C. It follows that every category has an underlying groupoid.
; The automorphism group of an object X in a category is the hom class Hom(X,X) of X
; in the underlying groupoid. It follows that the definition of automorphism groups involves
; two components: the enumeration theory of hom classes and the construction of
; underlying groupoids of categories.

; The special case of sets
(defn set-automorphism-group
  [coll]

  (->Group
    (bijective-set-hom coll coll)
    (fn [[a b]]
      (compose a b))
    (identity-function coll)
    invert-function))

; Computation of automorphism groups by a multimethod
(defmulti aut type)

(defmethod aut :default
  [coll]

  (set-automorphism-group coll))

(defmethod aut SetFunction
  [func]

  (->Monoid
    (function-isomorphisms func func)
    (fn [[a b]]
      (compose a b))
    (identity-morphism func)))

(defmethod aut Diset
  [pair]

  (->Monoid
    (diset-isomorphisms pair pair)
    (fn [[a b]]
      (compose a b))
    (identity-morphism pair)))

(defmethod aut Bijection
  [func]

  (->Monoid
    (bijection-isomorphisms func func)
    (fn [[a b]]
      (compose a b))
    (identity-morphism func)))