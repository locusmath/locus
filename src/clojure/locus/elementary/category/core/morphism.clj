(ns locus.elementary.category.core.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.order.core.monotone-map :refer :all])
  (:import (locus.elementary.lattice.core.morphism LatticeMorphism)
           (locus.elementary.function.core.object SetFunction)
           (locus.elementary.category.core.object Category)
           (locus.elementary.semigroup.monoid.morphism MonoidMorphism)
           (locus.elementary.order.core.monotone_map MonotoneMap)))

; Let Cat be the category of categories. Then Cat has categories as its objects and
; functors as morphisms. In this file we describe our implementation of the morphisms
; in the category of categories. We also provide the morphism part of all the
; fundamental copresheaf valued functors of the category of categories.
(deftype Functor [source target morphism-function object-function]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function)

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    (->MorphismOfQuivers
      (underlying-quiver source)
      (underlying-quiver target)
      (SetFunction. (first-set source) (first-set target) morphism-function)
      (SetFunction. (second-set source) (second-set target) object-function)))

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (->Diamond
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      (SetFunction.
        (inputs (source-object this))
        (inputs (target-object this))
        (fn [[morphism1 morphism2]]
          (list
            (morphism-function morphism1)
            (morphism-function morphism2))))
      (SetFunction.
        (outputs (source-object this))
        (outputs (target-object this))
        morphism-function))))

; The position of functors within the type hierarchy
(derive Functor :locus.elementary.function.core.protocols/functor)

; Classes of functors
(defn endofunctor?
  [func]

  (and
    (functor? func)
    (= (source-object func) (target-object func))))

(defn endosemifunctor?
  [func]

  (and
    (semifunctor? func)
    (= (source-object func) (target-object func))))

; The underlying monotone map of a functor, along with the underlying preposet
; of a category together define a functor from the category of categories
; to the category of thin categories and monotone maps.
(defn underlying-monotone-map
  [func]

  (->MonotoneMap
    (underlying-preposet (source-object func))
    (underlying-preposet (target-object func))
    (second-function func)))

; Monotone maps are functors of thin categories
; Therefore, they can be added to our ontology of functors and semifunctors.
(defn monotone-map?
  [func]

  (and
    (functor? func)
    (thin-category? (source-object func))
    (thin-category? (target-object func))))

; Applications
(defn object-apply
  [functor obj]

  ((second-function functor) obj))

(defn morphism-apply
  [functor morphism]

  ((first-function functor) morphism))

(defn source-objects
  [functor]

  (objects (source-object functor)))

(defn source-morphisms
  [functor]

  (morphisms (source-object functor)))

(defn target-objects
  [functor]

  (objects (target-object functor)))

(defn target-morphisms
  [functor]

  (morphisms (target-object functor)))

; Composition and identities in the category of categories
(defmethod compose* Functor
  [^Functor f ^Functor g]

  (Functor.
    (source-object g)
    (target-object f)
    (comp (.morphism-function f) (.morphism_function g))
    (comp (.object-function f) (.object-function g))))

(defmethod identity-morphism :locus.elementary.function.core.protocols/category
  [category]

  (Functor. category category identity identity))

; Functorial conversions
(defmulti to-functor type)

(defmethod to-functor Functor
  [func] func)

(defmethod to-functor LatticeMorphism
  [func]

  (Functor.
    (to-category (source-object func))
    (to-category (target-object func))
    (fn [[a b]]
      (list (func a) (func b)))
    func))

(defmethod to-functor MonotoneMap
  [func]

  (Functor.
    (to-category (source-object func))
    (to-category (target-object func))
    (first-function func)
    (second-function func)))

(defmethod to-functor MonoidMorphism
  [func]

  (Functor.
    (to-category (source-object func))
    (to-category (target-object func))
    func
    identity))

; We need support for some essential predicates for dealing with functors
; parallel functors in particular are the objects of natural transformations
(defn parallel-functors?
  [a b]

  (and
    (functor? a)
    (functor? b)
    (= (source-object a) (source-object b))
    (= (target-object a) (target-object b))))

