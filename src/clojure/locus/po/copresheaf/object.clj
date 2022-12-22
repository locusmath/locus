(ns locus.po.copresheaf.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.copresheaf.quiver.unital.morphism :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.algebra.category.concrete.object :refer :all]
            [locus.algebra.category.concrete.categories :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.core.morphism :refer :all]
            [locus.order.general.core.isomorphism :refer :all])
  (:import (locus.order.general.core.object Preposet)
           (locus.order.general.core.morphism MonotoneMap)
           (locus.set.copresheaf.topoi.copresheaf.object Copresheaf)
           (locus.order.general.core.isomorphism PreorderIsomorphism)))

; Let S be a set then Ord(S) is its lattice of preorders. This generalizes naturally to the
; context of copresheaves. Let F : C -> Sets be a copresheaf, then Ord(F) is its lattice of
; of preorders. Each element of this lattice is a presheaf of preorders, which is a functor
; to the concrete category of preorders, with F as its underlying copresheaf. Every
; construction in Locus is generalized from sets to presheaves, so we have generalized
; preorders to occur on presheaves instead of simply sets.

; Preordered copresheaves are part of the structure copresheaf framework. This means that
; each object has its own underlying set and each arrow has its own underlying function.
; These can be accessed using the get-object, get-morphism, get-set, and get-function
; methods with the objects and morphisms of the index category. The index category of
; a preordered copresheaf can be accessed by its index method. The target category is
; always the concrete category of preorders and monotone maps.

(deftype PreorderedCopresheaf [index object-function morphism-function]
  AbstractMorphism
  (source-object [this] index)
  (target-object [this] nil)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive PreorderedCopresheaf :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Structure copresheaf framework methods
(defmethod get-object PreorderedCopresheaf
  [functor x]

  ((second-function functor) x))

(defmethod get-morphism PreorderedCopresheaf
  [functor x]

  ((first-function functor) x))

(defmethod get-set PreorderedCopresheaf
  [functor x]

  (underlying-set (get-object functor x)))

(defmethod get-function PreorderedCopresheaf
  [functor x]

  (underlying-function (get-morphism functor x)))

(defmethod index PreorderedCopresheaf
  [^PreorderedCopresheaf functor] (.-index functor))

; Conversion routines to convert presheaves of preorders into other objects
(defmethod to-functor PreorderedCopresheaf
  [functor]

  (->Functor
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

(defmethod to-copresheaf PreorderedCopresheaf
  [functor]

  (->Copresheaf
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Constructors for special types of preordered copresheaves
(defn preordered-diset
  [a b]

  (->PreorderedCopresheaf
    (thin-category (weak-order [#{0 1}]))
    (fn [obj]
      (case obj
        0 a
        1 b))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism a)
        [1 1] (identity-morphism b)))))

; Conversion routines to take other objects and turn them into presheaves of preorders
(defmulti to-preordered-copresheaf type)

(defmethod to-preordered-copresheaf PreorderedCopresheaf
  [functor] functor)

(defmethod to-preordered-copresheaf Preposet
  [preorder]

  (->PreorderedCopresheaf
    (thin-category (weak-order [#{0}]))
    (constantly preorder)
    (constantly (identity-morphism preorder))))

(defmethod to-preordered-copresheaf MonotoneMap
  [morphism]

  (->PreorderedCopresheaf
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object morphism)
        1 (target-object morphism)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism (source-object morphism))
        [1 1] (identity-morphism (target-object morphism))
        [0 1] morphism))))

(defmethod to-preordered-copresheaf PreorderIsomorphism
  [isomorphism]

  (->PreorderedCopresheaf
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object isomorphism)
        1 (target-object isomorphism)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-morphism (source-object isomorphism))
        [1 1] (identity-morphism (target-object isomorphism))
        [0 1] isomorphism
        [1 0] (inv isomorphism)))))

(defmethod to-preordered-copresheaf :locus.set.logic.structure.protocols/copresheaf
  [copresheaf]

  (->PreorderedCopresheaf
    (index copresheaf)
    (fn [obj]
      (discrete-preorder (get-set copresheaf obj)))
    (fn [arrow]
      (discrete-monotone-map (get-function copresheaf arrow)))))

; Ontology of presheaves of preorders
(defn preordered-copresheaf?
  [copresheaf]

  (= (type copresheaf) PreorderedCopresheaf))

(defn preordered-set?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (= (count (objects cat))
         (count (morphisms cat))
         1))))

(defn preordered-function?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (total-order-category? cat)
        (= (count (objects cat)) 2)))))

(defn preordered-diset?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (discrete-category? cat)
        (= (count (objects cat)) 2)))))

(defn preordered-nset?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (discrete-category? (index copresheaf))))

(defn preordered-quiver?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (n-arrow-category? cat)
        (= (count (morphisms cat)) 4)))))

(defn preordered-ternary-quiver?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (n-arrow-category? cat)
        (= (count (morphisms cat)) 5)))))

(defn preordered-nary-quiver?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (n-arrow-category? (index copresheaf))))

(defn preordered-bijection?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (complete-thin-groupoid? cat)
        (= (count (objects cat)) 2)))))

(defn preordered-chain?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (total-order-category? (index copresheaf))))

(defn preordered-triangle?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (let [cat (index copresheaf)]
      (and
        (total-order-category? cat)
        (= (count (objects cat)) 3)))))

(defn preordered-diamond?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (diamond-category? (index copresheaf))))

(defn preordered-mset?
  [copresheaf]

  (and
    (preordered-copresheaf? copresheaf)
    (= (count (objects (index copresheaf))) 1)))


