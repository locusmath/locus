(ns locus.structure.relational.functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (locus.elementary.category.relation.set_relation SetRelation)
           (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.category.core.morphism Functor)))

; A functor F: C -> Rel is a structure copresheaf through the intermediary functor f: Rel -> Sets
; which makes Rel into a concrete category. Therefore, relational functors implement both the
; get-object and get-morphism methods of functors and the get-set and get-function methods
; of copresheaves. The translation of relations to functions uses the image function class.
(deftype RelationalFunctor [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] rel)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive RelationalFunctor :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Get the objects and morphisms of relational functors
(defmethod get-morphism RelationalFunctor
  [functor x]

  ((first-function functor) x))

(defmethod get-object RelationalFunctor
  [functor x]

  ((second-function functor) x))

; Relational functors are structure copresheaves, so that
(defmethod get-set RelationalFunctor
  [functor x]

  (->PowerSet (get-object functor x)))

(defmethod get-function RelationalFunctor
  [functor x]

  (to-function (get-morphism functor x)))

; A relational functor is a structure copresheaf over a general index category
(defmethod index RelationalFunctor
  [^RelationalFunctor functor] (.-category functor))

; Conversion routines for relational functors
(defmulti to-relational-functor type)

(defmethod to-relational-functor RelationalFunctor
  [functor] functor)

(defmethod to-relational-functor :locus.base.logic.core.set/universal
  [coll]

  (RelationalFunctor.
    (thin-category (weak-order [#{0}]))
    (fn [obj]
      coll)
    (fn [morphism]
      (identity-relation coll))))

(defmethod to-relational-functor SetRelation
  [rel]

  (RelationalFunctor.
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object rel)
        1 (target-object rel)))
    (fn [[i j]]
      (case [i j]
        [0 0] (identity-relation (source-object rel))
        [1 1] (identity-relation (target-object rel))
        [0 1] rel))))

(defmethod to-relational-functor Copresheaf
  [copresheaf]

  (RelationalFunctor.
    (index copresheaf)
    (partial get-set copresheaf)
    (fn [func]
      (to-set-relation (get-function copresheaf func)))))

(defmethod to-relational-functor :default
  [obj] (to-relational-functor (to-copresheaf obj)))

; Conversion routines for relational functors
(defmethod to-functor RelationalFunctor
  [functor]

  (Functor.
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

; Get the underlying copresheaf of a functor to the allegory of relations
(defmethod to-copresheaf RelationalFunctor
  [^RelationalFunctor functor]

  (Copresheaf.
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Create relational quivers from functors to the allegory of relations
(defn nth-component-set-relation
  [edges vertices n]

  (->SetRelation
    edges
    vertices
    (fn [edge]
      (nth edge n))))

(defn set-relational-quiver
  [vertices edges]

  (RelationalFunctor.
    t2*
    (fn [obj]
      (case obj
        0 edges
        1 vertices))
    (fn [arrow]
      (case arrow
        0 (identity-relation edges)
        1 (identity-relation vertices)
        2 (->SetRelation edges vertices first)
        3 (->SetRelation edges vertices second)))))

(defn nary-set-relational-quiver
  [edges vertices n]

  (RelationalFunctor.
    (n-arrow-category n)
    (fn [obj]
      (case obj
        0 edges
        1 vertices))
    (fn [arrow]
      (cond
        (= arrow 0) (identity-relation edges)
        (= arrow 1) (identity-relation vertices)
        :else (nth-component-set-relation edges vertices (- n 2))))))

; Paths in the category Rel of sets and relations
(defn set-relational-triangle
  [f g]

  (RelationalFunctor.
    (thin-category (weak-order [#{0} #{1} #{2}]))
    (fn [obj]
      (case obj
        0 (source-object g)
        1 (target-object g)
        2 (target-object f)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-relation (source-object g))
        [0 1] f
        [0 2] (compose f g)
        [1 1] (identity-relation (target-object g))
        [1 2] g
        [2 2] (identity-relation (target-object f))))))

; A change of category routine for relational functors
(defn change-relational-functor-index-category
  [functor relational-functor]

  (RelationalFunctor.
    (source-object functor)
    (fn [obj]
      (get-object relational-functor (get-object functor obj)))
    (fn [arrow]
      (get-morphism relational-functor (get-morphism functor arrow)))))

; Ontology of relational functors
(defn relational-functor?
  [functor]

  (= (type functor) RelationalFunctor))

(defn set-relational-quiver?
  [functor]

  (and
    (relational-functor? functor)
    (two-arrow-category? (index functor))))

(defn set-relational-nary-quiver?
  [functor]

  (and
    (relational-functor? functor)
    (n-arrow-category? (index functor))))

(defn set-relational-chain?
  [functor]

  (and
    (relational-functor? functor)
    (total-order-category? (index functor))))

(defn set-relational-triangle?
  [functor]

  (and
    (relational-functor? functor)
    (total-order-category? (index functor))
    (= (count (objects (index functor))) 3)))
