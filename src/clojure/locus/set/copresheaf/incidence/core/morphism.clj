(ns locus.set.copresheaf.incidence.core.morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.copresheaf.incidence.core.object :refer :all])
  (:import (locus.set.copresheaf.incidence.core.object Span)))

; Morphisms in the topos Sets^{[1,2]} of span copresheaves
; Morphisms of spans have three components: a flag component function, an edge component function,
; and a vertex component function. Together they make up the data of a natural transformation.
; A morphism of spans can also be treated as a presheaf in the topos Sets^{T_2 x [1,2]} so it
; has all attendant presheaf theoretic functionality associated with it such as products,
; coproducts, subobjects, and quotients.

(deftype MorphismOfSpans [source-span target-span ffn efn vfn]
  AbstractMorphism
  (source-object [this]
    source-span)
  (target-object [this]
    target-span)

  ConcreteMorphism
  (inputs [this] (underlying-set (source-object this)))
  (outputs [this] (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (ffn v))
      (= i 1) (list 1 (efn v))
      (= i 2) (list 2 (vfn v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MorphismOfSpans :locus.set.logic.structure.protocols/structured-function)

; Component functions of span morphisms in the topos Sets^{[1,1] x [2,1]}
(defn span-flag-function
  [^MorphismOfSpans morphism]

  (->SetFunction
    (span-flags (source-object morphism))
    (span-flags (target-object morphism))
    (.-ffn morphism)))

(defn span-edge-function
  [^MorphismOfSpans morphism]

  (->SetFunction
    (span-edges (source-object morphism))
    (span-edges (target-object morphism))
    (.-efn morphism)))

(defn span-vertex-function
  [^MorphismOfSpans morphism]

  (->SetFunction
    (span-vertices (source-object morphism))
    (span-vertices (target-object morphism))
    (.-vfn morphism)))

(defn span-morphism-component-function
  [morphism n]

  (case n
    0 (span-flag-function morphism)
    1 (span-edge-function morphism)
    2 (span-vertex-function morphism)))

; Components of morphisms of spans
(defmethod get-set MorphismOfSpans
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function MorphismOfSpans
  [morphism [[i v] [j w]]]

  (case [i j]
    [0 0] (get-function (source-object morphism) [v w])
    [1 1] (get-function (target-object morphism) [v w])
    [0 1] (compose
            (get-function (target-object morphism) [v w])
            (span-morphism-component-function morphism v))))

; Inclusions of span copresheaves
(defn inclusion-of-spans
  [span a b c]

  (MorphismOfSpans.
    (subspan span a b c)
    span
    (inclusion-function a (span-flags span))
    (inclusion-function b (span-edges span))
    (inclusion-function c (span-vertices span))))

; Composition and identities in the topos of span copresheaves
(defmethod compose* MorphismOfSpans
  [^MorphismOfSpans a, ^MorphismOfSpans b]

  (MorphismOfSpans.
    (source-object b)
    (target-object a)
    (comp (.ffn a) (.ffn b))
    (comp (.efn a) (.efn b))
    (comp (.vfn a) (.vfn b))))

(defmethod identity-morphism Span
  [^Span span]

  (MorphismOfSpans.
    span
    span
    (identity-function (span-flags span))
    (identity-function (span-edges span))
    (identity-function (span-vertices span))))

; Products and coproducts in the topos Sets^{[1,2] x [1,1]}
(defmethod product MorphismOfSpans
  [& args]

  (MorphismOfSpans.
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map span-flag-function args))
    (apply product (map span-edge-function args))
    (apply product (map span-vertex-function args))))

(defmethod coproduct MorphismOfSpans
  [& args]

  (MorphismOfSpans.
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map span-flag-function args))
    (apply coproduct (map span-edge-function args))
    (apply coproduct (map span-vertex-function args))))

; Subobject classifiers in the topos Sets^{[1,2]}
(def truth-span
  (Span.
    '#{(0 0) (1/2 0) (0 1/2) (1/2 1/2) (1 1)}
    #{0 1}
    #{0 1}
    (fn [[a b]]
      (if (= a 0) 0 1))
    (fn [[a b]]
      (if (= b 0) 0 1))))

(defn subspan-character
  [span new-flags new-edges new-vertices]

  (->MorphismOfSpans
    span
    truth-span
    (fn [flag]
      (if (contains? new-flags flag)
        (list 1 1)
        (list
          (cond
            (contains? new-edges (edge-component span flag)) 1/2
            :else 0)
          (cond
            (contains? new-vertices (vertex-component span flag)) 1/2
            :else 0))))
    (fn [edge]
      (cond
        (contains? new-edges edge) 1
        :else 0))
    (fn [vertex]
      (cond
        (contains? new-vertices vertex) 1
        :else 0))))

; Ontology of morphisms of spans
(defn morphism-of-spans?
  [morphism]

  (= (type morphism) MorphismOfSpans))

; Morphism of spans
(defmethod visualize MorphismOfSpans
  [^MorphismOfSpans morphism]

  (let [first-span (source-object morphism)
        second-span (target-object morphism)
        [p v] (generate-copresheaf-data
                {0 (span-flags first-span)
                 1 (span-edges first-span)
                 2 (span-vertices first-span)
                 3 (span-flags second-span)
                 4 (span-edges second-span)
                 5 (span-vertices second-span)}
                #{(list 0 1 (edge-function first-span))
                  (list 0 2 (vertex-function first-span))
                  (list 3 5 (edge-function second-span))
                  (list 4 5 (edge-function second-span))
                  (list 0 3 (span-flag-function morphism))
                  (list 1 4 (span-edge-function morphism))
                  (list 2 5 (span-vertex-function morphism))})]
    (visualize-clustered-digraph* "BT" p v)))
