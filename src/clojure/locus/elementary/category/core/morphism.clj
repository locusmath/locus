(ns locus.elementary.category.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.unital.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.preorder.core.morphism :refer :all])
  (:import (locus.elementary.lattice.core.morphism LatticeMorphism)
           (locus.base.function.core.object SetFunction)
           (locus.elementary.semigroup.monoid.morphism MonoidMorphism)
           (locus.elementary.preorder.core.morphism MonotoneMap)))

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
    (morphism-of-partial-binary-operations
      (underlying-function (source-object this))
      (underlying-function (target-object this))
      morphism-function)))

; The position of functors within the type hierarchy
(derive Functor :locus.elementary.copresheaf.core.protocols/functor)

; Index categories for functors
(defmethod index Functor
  [functor] (source-object functor))

; Composition and identities in the category of categories
(defmethod compose* :locus.elementary.copresheaf.core.protocols/functor
  [^Functor f ^Functor g]

  (Functor.
    (source-object g)
    (target-object f)
    (comp (.morphism_function f) (.morphism_function g))
    (comp (.object_function f) (.object_function g))))

(defmethod identity-morphism :locus.elementary.copresheaf.core.protocols/category
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

; Monotone maps are functors of thin categories
; Therefore, they can be added to our ontology of functors and semifunctors.
(defn monotone-map?
  [func]

  (and
    (functor? func)
    (thin-category? (source-object func))
    (thin-category? (target-object func))))

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

; Classes of functors
(defn endofunctor?
  [func]

  (and
    (functor? func)
    (= (source-object func) (target-object func))))

