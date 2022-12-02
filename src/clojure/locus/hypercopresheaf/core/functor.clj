(ns locus.hypercopresheaf.core.functor
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.binary.core.morphism :refer :all]
            [locus.mapping.multivalued.hyperfunction :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.concrete.concrete-category :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.category.concrete.categories :refer :all]
            [locus.hyperquiver.core.object :refer :all])
  (:import (locus.mapping.multivalued.hyperfunction Hyperfunction)
           (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.category.core.morphism Functor)))

; A functor F: C -> Rel is a structure copresheaf through the intermediary functor f: Rel -> Sets
; which makes Rel into a concrete category. Therefore, relational functors implement both the
; get-object and get-morphism methods of functors and the get-set and get-function methods
; of copresheaves. The translation of relations to functions uses the image function class.
(deftype Hypercopresheaf [category object-function morphism-function]
  AbstractMorphism
  (source-object [this] category)
  (target-object [this] rel)

  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(derive Hypercopresheaf :locus.elementary.copresheaf.core.protocols/structure-copresheaf)

; Get the objects and morphisms of relational functors
(defmethod get-morphism Hypercopresheaf
  [functor x]

  ((first-function functor) x))

(defmethod get-object Hypercopresheaf
  [functor x]

  ((second-function functor) x))

; Relational functors are structure copresheaves, so that
(defmethod get-set Hypercopresheaf
  [functor x]

  (->PowerSet (get-object functor x)))

(defmethod get-function Hypercopresheaf
  [functor x]

  (to-function (get-morphism functor x)))

; A relational functor is a structure copresheaf over a general index category
(defmethod index Hypercopresheaf
  [^Hypercopresheaf functor] (.-category functor))

; A hypercopresheaf is a functor to the concrete allegory rel
(defmethod index Hypercopresheaf
  [^Hypercopresheaf functor] (.-category functor))

; Conversion routines for relational functors
(defmulti to-hypercopresheaf type)

(defmethod to-hypercopresheaf Hypercopresheaf
  [functor] functor)

(defmethod to-hypercopresheaf :locus.base.logic.core.set/universal
  [coll]

  (Hypercopresheaf.
    (thin-category (weak-order [#{0}]))
    (fn [obj]
      coll)
    (fn [morphism]
      (identity-hyperfunction coll))))

(defmethod to-hypercopresheaf Hyperfunction
  [rel]

  (Hypercopresheaf.
    (thin-category (weak-order [#{0} #{1}]))
    (fn [obj]
      (case obj
        0 (source-object rel)
        1 (target-object rel)))
    (fn [[i j]]
      (case [i j]
        [0 0] (identity-hyperfunction (source-object rel))
        [1 1] (identity-hyperfunction (target-object rel))
        [0 1] rel))))

(defmethod to-hypercopresheaf Copresheaf
  [copresheaf]

  (Hypercopresheaf.
    (index copresheaf)
    (partial get-set copresheaf)
    (fn [func]
      (to-hyperfunction (get-function copresheaf func)))))

(defmethod to-hypercopresheaf :default
  [obj] (to-hypercopresheaf (to-copresheaf obj)))

; Conversion routines for relational functors
(defmethod to-functor Hypercopresheaf
  [functor]

  (Functor.
    (source-object functor)
    (target-object functor)
    (partial get-object functor)
    (partial get-morphism functor)))

; Get the underlying copresheaf of a functor to the concrete allegory of relations
(defmethod to-copresheaf Hypercopresheaf
  [^Hypercopresheaf functor]

  (Copresheaf.
    (index functor)
    (partial get-set functor)
    (partial get-function functor)))

; Create relational quivers from functors to the allegory of relations
(defn relational-nth-component-hyperfunction
  [edges vertices n]

  (->Hyperfunction
    edges
    vertices
    (fn [edge]
      (nth edge n))))

(defn hyperquiver-copresheaf
  [vertices edges]

  (Hypercopresheaf.
    t2*
    (fn [obj]
      (case obj
        0 edges
        1 vertices))
    (fn [arrow]
      (case arrow
        0 (identity-hyperfunction edges)
        1 (identity-function vertices)
        2 (->Hyperfunction edges vertices first)
        3 (->Hyperfunction edges vertices second)))))

(defn nary-hyperquiver-copresheaf
  [edges vertices n]

  (Hypercopresheaf.
    (n-arrow-category n)
    (fn [obj]
      (case obj
        0 edges
        1 vertices))
    (fn [arrow]
      (cond
        (= arrow 0) (identity-hyperfunction edges)
        (= arrow 1) (identity-hyperfunction vertices)
        :else (relational-nth-component-hyperfunction edges vertices (- n 2))))))

; Paths in the category Rel of sets and relations
(defn hypertriangle
  [f g]

  (Hypercopresheaf.
    (thin-category (weak-order [#{0} #{1} #{2}]))
    (fn [obj]
      (case obj
        0 (source-object g)
        1 (target-object g)
        2 (target-object f)))
    (fn [[a b]]
      (case [a b]
        [0 0] (identity-hyperfunction (source-object g))
        [0 1] f
        [0 2] (compose f g)
        [1 1] (identity-hyperfunction (target-object g))
        [1 2] g
        [2 2] (identity-hyperfunction (target-object f))))))

; A change of category routine for relational functors
(defn change-relational-functor-index-category
  [functor relational-functor]

  (Hypercopresheaf.
    (source-object functor)
    (fn [obj]
      (get-object relational-functor (get-object functor obj)))
    (fn [arrow]
      (get-morphism relational-functor (get-morphism functor arrow)))))

; Ontology of hypercopresheaves
(defn hypercopresheaf?
  [functor]

  (= (type functor) Hypercopresheaf))

(defn object-hypercopresheaf?
  [functor]

  (and
    (hypercopresheaf? functor)
    (let [cat (index functor)]
      (and
        (= (count (objects cat)) 1)
        (total-order-category? cat)))))

(defn function-hypercopresheaf?
  [functor]

  (and
    (hypercopresheaf? functor)
    (let [cat (index functor)]
      (and
        (= (count (objects cat)) 2)
        (total-order-category? cat)))))

(defn binary-quiver-hypercopresheaf?
  [functor]

  (and
    (hypercopresheaf? functor)
    (two-arrow-category? (index functor))))

(defn nary-quiver-hypercopresheaf?
  [functor]

  (and
    (hypercopresheaf? functor)
    (n-arrow-category? (index functor))))

(defn hyperchain?
  [functor]

  (and
    (hypercopresheaf? functor)
    (total-order-category? (index functor))))

(defn hypertriangle?
  [functor]

  (and
    (hypercopresheaf? functor)
    (let [index-category (index functor)]
      (and
        (= (count (objects index-category)) 3)
        (total-order-category? index-category)))))

(defn hyperdiamond?
  [functor]

  (and
    (hypercopresheaf? functor)
    (diamond-category? (index functor))))

(defn hyperspan?
  [functor]

  (and
    (hypercopresheaf? functor)
    (let [cat (index functor)]
      (and
        (= (count (objects cat)) 3)
        (n-span-category? cat)))))

(defn hypercospan?
  [functor]

  (and
    (hypercopresheaf? functor)
    (let [cat (index functor)]
      (and
        (= (count (objects cat)) 3)
        (n-cospan-category? cat)))))

(defn set-relational-triangle?
  [functor]

  (and
    (hypercopresheaf? functor)
    (total-order-category? (index functor))
    (= (count (objects (index functor))) 3)))