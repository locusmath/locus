(ns locus.set.tree.triangle.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.tree.triangle.core.object :refer :all])
  (:import (locus.set.tree.triangle.core.object SetTriangle)))

; Morphism in the topos of triangles Sets^{T_3}
; Morphisms in triangles have three components ordered one after another which describe the component
; morphisms for each of the objects in the base index category T_3 of the copresheaf topos that
; forms the category of triangle copresheaves. At the same time, morphisms of triangles are
; themselves presheaves in the topos Sets^{T_2 x T_3} which means that they have all attendant
; presheaf topos theoretic properties associated with them such as products, coproducts,
; subobjects and quotients.

(deftype TriangleMorphism [source-triangle target-triangle sfn mfn tfn]
  AbstractMorphism
  (source-object [this]
    source-triangle)
  (target-object [this]
    target-triangle)

  ConcreteMorphism
  (inputs [this] (underlying-set (source-object this)))
  (outputs [this] (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i '(0 0)) (list '(0 0) (sfn v))
      (= i '(0)) (list '(0) (mfn v))
      (= i '()) (list '() (tfn v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive TriangleMorphism :locus.set.logic.structure.protocols/morphism-of-copresheaves)

; Triangle component functions
(defn triangle-source-function
  [^TriangleMorphism func]

  (->SetFunction
    (triangle-source (source-object func))
    (triangle-source (target-object func))
    (.-sfn func)))

(defn triangle-middle-function
  [^TriangleMorphism func]

  (->SetFunction
    (triangle-middle (source-object func))
    (triangle-middle (target-object func))
    (.-mfn func)))

(defn triangle-target-function
  [^TriangleMorphism func]

  (->SetFunction
    (triangle-target (source-object func))
    (triangle-target (target-object func))
    (.-tfn func)))

(defn triangle-morphism-component-function
  [triangle n]

  (cond
    (= n '(0 0)) (triangle-source-function triangle)
    (= n '(0)) (triangle-middle-function triangle)
    (= n '()) (triangle-target-function triangle)))

; Components of morphisms of triangles
(defmethod get-set TriangleMorphism
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function TriangleMorphism
  [morphism [[i v] [j w]]]

  (case [i j]
    [0 0] (get-function (source-object morphism) [v w])
    [1 1] (get-function (target-object morphism) [v w])
    [0 1] (compose
            (get-function (target-object morphism) [v w])
            (triangle-morphism-component-function morphism v))))

; Composition and identities in the topos of triangles
(defmethod compose* TriangleMorphism
  [^TriangleMorphism a, ^TriangleMorphism b]

  (TriangleMorphism.
    (source-object b)
    (target-object a)
    (comp (.sfn a) (.sfn b))
    (comp (.mfn a) (.mfn b))
    (comp (.tfn a) (.tfn b))))

(defmethod identity-morphism SetTriangle
  [^TriangleMorphism triangle]

  (TriangleMorphism.
    triangle
    triangle
    (identity-function (triangle-source triangle))
    (identity-function (triangle-middle triangle))
    (identity-function (triangle-target triangle))))

; Products and coproducts in hte topos of morphisms of triangles
(defmethod product TriangleMorphism
  [& morphisms]

  (->TriangleMorphism
    (apply product (map source-object morphisms))
    (apply product (map target-object morphisms))
    (apply product (map triangle-source-function morphisms))
    (apply product (map triangle-middle-function morphisms))
    (apply product (map triangle-target-function morphisms))))

(defmethod coproduct TriangleMorphism
  [& morphisms]

  (->TriangleMorphism
    (apply coproduct (map source-object morphisms))
    (apply coproduct (map target-object morphisms))
    (apply coproduct (map triangle-source-function morphisms))
    (apply coproduct (map triangle-middle-function morphisms))
    (apply coproduct (map triangle-target-function morphisms))))

; A copresheaf in the topos Sets^{T_2 x T_3} is a morphism of triangles, but equal it
; could also be considered to be a pair of diamonds.
(defn presquare
  [morphism]

  (->SetSquare
    (prefunction (source-object morphism))
    (prefunction (target-object morphism))
    (triangle-source-function morphism)
    (triangle-middle-function morphism)))

(defn postsquare
  [morphism]

  (->SetSquare
    (postfunction (source-object morphism))
    (postfunction (target-object morphism))
    (triangle-middle-function morphism)
    (triangle-target-function morphism)))

(defn compsquare
  [morphism]

  (->SetSquare
    (compfunction (source-object morphism))
    (compfunction (target-object morphism))
    (triangle-source-function morphism)
    (triangle-target-function morphism)))

; Combine two diamonds to form a morphism of triangles
(defn combine-squares
  [f g]

  (->TriangleMorphism
    (->SetTriangle (first-function f) (first-function g))
    (->SetTriangle (second-function f) (second-function g))
    (source-object g)
    (target-object g)
    (target-object f)))

; Create a morphism of triangles by inclusion referring to a subobject
(defn inclusion-of-triangles
  [triangle new-source new-middle new-target]

  (TriangleMorphism.
    (subtriangle triangle new-source new-middle new-target)
    triangle
    (inclusion-function new-source (triangle-source triangle))
    (inclusion-function new-middle (triangle-middle triangle))
    (inclusion-function new-target (triangle-target triangle))))

; Subobject classifiers in the topos Sets^{T_3}
(def truth-triangle
  (SetTriangle.
    (mapfn {0 0, 1/2 1, 1 1})
    (mapfn {0 0, 1/3 1/2, 2/3 1, 1 1})))

; Get the character of a subobject in the topos of triangles
(defn subtriangle-character
  [triangle new-source new-middle new-target]

  (TriangleMorphism.
    triangle
    truth-triangle
    (fn [source-element]
      (cond
        (contains? new-source source-element) 1
        (contains? new-middle ((prefunction triangle) source-element)) 2/3
        (contains? new-target ((compfunction triangle) source-element)) 1/3
        :else 0))
    (fn [middle-element]
      (cond
        (contains? new-middle middle-element) 1
        (contains? new-target ((postfunction triangle) middle-element)) 1/2
        :else 0))
    (fn [target-element]
      (if (contains? new-target target-element)
        1
        0))))

; Ontology of homomorphisms of triangle copresheaves
(defn morphism-of-triangles?
  [morphism]

  (= (type morphism) TriangleMorphism))

; Morphism of triangles
(defmethod visualize TriangleMorphism
  [^TriangleMorphism morphism]

  (let [first-triangle (source-object morphism)
        second-triangle (target-object morphism)
        [p v] (generate-copresheaf-data
                {0 (triangle-source first-triangle)
                 1 (triangle-middle first-triangle)
                 2 (triangle-target first-triangle)
                 3 (triangle-source second-triangle)
                 4 (triangle-middle second-triangle)
                 5 (triangle-target second-triangle)}
                #{(list 0 1 (prefunction first-triangle))
                  (list 1 2 (postfunction first-triangle))
                  (list 3 4 (prefunction second-triangle))
                  (list 4 5 (postfunction second-triangle))
                  (list 0 3 (triangle-source-function morphism))
                  (list 1 4 (triangle-middle-function morphism))
                  (list 2 5 (triangle-target-function morphism))})]
    (visualize-clustered-digraph* "LR" p v)))
