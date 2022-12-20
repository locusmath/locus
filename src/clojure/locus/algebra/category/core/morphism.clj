(ns locus.algebra.category.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.unary.core.morphism :refer :all]
            [locus.set.quiver.diset.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.semigroup.monoid.morphism :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.core.morphism :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.core.morphism LatticeMorphism)
           (locus.set.mapping.general.core.object SetFunction)
           (locus.algebra.semigroup.monoid.morphism MonoidMorphism)
           (locus.order.general.core.morphism MonotoneMap)))

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

  ConcreteHigherMorphism
  (underlying-morphism-of-functions [this]
    (morphism-of-partial-binary-operations
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      morphism-function)))

; The position of functors within the type hierarchy
(derive Functor :locus.set.copresheaf.structure.core.protocols/functor)

; Index categories for functors
(defmethod index Functor
  [functor] (source-object functor))

; Composition and identities in the category of categories
(defmethod compose* :locus.set.copresheaf.structure.core.protocols/functor
  [^Functor f ^Functor g]

  (Functor.
    (source-object g)
    (target-object f)
    (comp (.morphism_function f) (.morphism_function g))
    (comp (.object_function f) (.object_function g))))

(defmethod identity-morphism :locus.set.copresheaf.structure.core.protocols/category
  [category]

  (Functor. category category identity identity))

; Compute a categorical elements function for a functor
(defn categorical-elements-function
  [functor]

  (->SetFunction
    (categorical-elements (source-object functor))
    (categorical-elements (target-object functor))
    (fn [[i v]]
      (case i
        0 (list 0 (morphism-apply functor v))
        1 (list 1 (object-apply functor v))))))

; The underlying monotone map of a functor, along with the underlying preposet
; of a category together define a functor from the category of categories
; to the category of thin categories and monotone maps.
(defn underlying-monotone-map
  [func]

  (->MonotoneMap
    (underlying-preposet (source-object func))
    (underlying-preposet (target-object func))
    (second-function func)))

; Turn a set function f: A -> B into a functor between discrete categories
(defn discrete-functor
  [func]

  (->Functor
    (discrete-category (inputs func))
    (discrete-category (outputs func))
    (fn [[a b]]
      (list (func a) (func b)))
    (fn [obj]
      (func obj))))

; Applications
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

; Get all objects or all morphisms of a functor
(defn all-objects
  [functor]

  (set
    (map
      (partial get-object functor)
      (objects (index functor)))))

(defn all-morphisms
  [functor]

  (set
    (map
      (partial get-morphism functor)
      (morphisms (index functor)))))

; Constant functors are outputs of diagonal functors
(defn constant-functor
  [source target target-object]

  (->Functor
    source
    target
    (constantly (identity-morphism-of target target-object))
    (constantly target-object)))

; Create special types of functors
(defn object-functor
  [category obj]

  (->Functor
    (thin-category (weak-order [#{0}]))
    category
    (constantly (identity-morphism-of category obj))
    (constantly obj)))

(defn arrow-functor
  [category morphism]

  (->Functor
    (thin-category (weak-order [#{0} #{1}]))
    category
    (fn [[a b]]
      (case [a b]
        [0 0] (source-identity category morphism)
        [1 1] (target-identity category morphism)
        [0 1] morphism))
    (fn [obj]
      (case obj
        0 (source-element category morphism)
        1 (target-element category morphism)))))

(defn path-functor
  [category [f g]]

  (->Functor
    (thin-category (weak-order [#{0} #{1} #{2}]))
    category
    (fn [[a b]]
      (case [a b]
        [0 0] (source-identity category g)
        [0 1] g
        [0 2] (category (list f g))
        [1 1] (target-identity category g)
        [1 2] f
        [2 2] (target-identity category f)))
    (fn [obj]
      (case obj
        0 (source-element category g)
        1 (target-element category g)
        2 (target-element category f)))))

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

; Determine which functors are actually monotone maps
(defmethod monotone-map? :default
  [func]

  (and
    (functor? func)
    (thin-category? (source-object func))
    (thin-category? (target-object func))))

; Classes of functors
(defn endofunctor?
  [func]

  (and
    (functor? func)
    (= (source-object func) (target-object func))))

