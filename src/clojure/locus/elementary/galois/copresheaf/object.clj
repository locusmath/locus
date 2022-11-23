(ns locus.elementary.galois.copresheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.base.effects.global.identity :refer :all]
            [locus.base.invertible.function.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all])
  (:import (locus.elementary.bijection.core.object Bijection)))

; A Galois copresheaf is a Galois connection minus any axioms of order theory. It is the
; presheaf theoretic concept that comes first before you consider actual Galois
; connections. Let C be the category with two objects A and B and two morphic generators
; F: A -> B and G: B -> A with the property that FG and GF are idempotent, and they
; fix F and G. It can be readily seen that such a copresheaf is simply a bijection
; between the fixed points of two idempotent transformations.

(deftype GaloisCopresheaf [source target f g]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  StructuredDiset
  (first-set [this] source)
  (second-set [this] target))

(derive GaloisCopresheaf :locus.elementary.copresheaf.core.protocols/structured-diset)

; Galois copresheaves have four non-identity functions
(defn left-function
  [^GaloisCopresheaf copresheaf]

  (.-f copresheaf))

(defn right-function
  [^GaloisCopresheaf copresheaf]

  (.-g copresheaf))

(defn source-transformation
  [^GaloisCopresheaf copresheaf]

  (comp (.-g copresheaf) (.-f copresheaf)))

(defn target-transformation
  [^GaloisCopresheaf copresheaf]

  (comp (.-f copresheaf) (.-g copresheaf)))

; Get the object and morphism components of galois copresheaves
(defmethod get-object GaloisCopresheaf
  [^GaloisCopresheaf copresheaf, x]

  (case x
    0 (first-set copresheaf)
    1 (second-set copresheaf)))

(defmethod get-morphism GaloisCopresheaf
  [^GaloisCopresheaf copresheaf, x]

  (case x
    0 (identity-function (first-set copresheaf))
    1 (identity-function (second-set copresheaf))
    2 (left-function copresheaf)
    3 (right-function copresheaf)
    4 (source-transformation copresheaf)
    5 (target-transformation copresheaf)))

; Get the underlying bijection of a Galois copresheaf
(defn source-fixed-points
  [^GaloisCopresheaf copresheaf]

  (let [func (source-transformation copresheaf)]
    (set
      (filter
        (fn [i]
          (= i (func i)))
        (inputs func)))))

(defn target-fixed-points
  [^GaloisCopresheaf copresheaf]

  (let [func (target-transformation copresheaf)]
    (set
      (filter
        (fn [i]
          (= i (func i)))
        (inputs func)))))

(defn fixed-points-bijection
  [^GaloisCopresheaf copresheaf]

  (let [f (left-function copresheaf)
        g (right-function copresheaf)]
    (->Bijection
      (source-fixed-points copresheaf)
      (target-fixed-points copresheaf)
      (fn [i]
        (f i))
      (fn [i]
        (g i)))))

; Generalized multimethods for converting objects and structures into galois copresheaves
(defmulti to-galois-copresheaf type)

(defmethod to-galois-copresheaf GaloisCopresheaf
  [^GaloisCopresheaf copresheaf] copresheaf)

(defmethod to-galois-copresheaf Bijection
  [^Bijection bijection]

  (->GaloisCopresheaf
    (inputs bijection)
    (outputs bijection)
    (.-forward bijection)
    (.-backward bijection)))

(defmethod to-galois-copresheaf :locus.base.logic.structure.protocols/invertible-set-function
  [func]

  (->GaloisCopresheaf
    (inputs func)
    (outputs func)
    func
    (inv func)))

; The topos of Galois copresheaves has all products and coproducts.
(defmethod product GaloisCopresheaf
  [& copresheaves]

  (->GaloisCopresheaf
    (apply product (map source-object copresheaves))
    (apply product (map target-object copresheaves))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((left-function (nth copresheaves i)) v))
        coll))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((right-function (nth copresheaves i)) v))
        coll))))

(defmethod coproduct GaloisCopresheaf
  [& copresheaves]

  (->GaloisCopresheaf
    (apply coproduct (map source-object copresheaves))
    (apply coproduct (map target-object copresheaves))
    (fn [[i v]]
      (list i ((left-function (nth copresheaves i)) v)))
    (fn [[i v]]
      (list i ((right-function (nth copresheaves i)) v)))))

; The definition of Galois copresheaves is self-dual
(defmethod dual GaloisCopresheaf
  [^GaloisCopresheaf copresheaf]

  (->GaloisCopresheaf
    (target-object copresheaf)
    (source-object copresheaf)
    (.-g copresheaf)
    (.-f copresheaf)))

; Ontology of galois copresheaves
(defn galois-copresheaf?
  [obj]

  (= (type obj) GaloisCopresheaf))

(defn galois-correspondence-copresheaf?
  [obj]

  (and
    (galois-copresheaf? obj)
    (equal-universals? (inputs obj) (source-fixed-points obj))
    (equal-universals? (outputs obj) (target-fixed-points obj))))