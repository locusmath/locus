(ns locus.elementary.cospan.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.cospan.core.object :refer :all])
  (:import (locus.elementary.cospan.core.object Cospan)))

; Morphisms in the topos of cospan copresheaves Sets^[2,1]
; Morphisms of cospans have three components: a first source function, a second source function,
; and a target function. Together they make up the components of a natural transformation.
(deftype MorphismOfCospans [source-cospan target-cospan afn bfn cfn]
  AbstractMorphism
  (source-object [this]
    source-cospan)
  (target-object [this]
    target-cospan)

  ConcreteMorphism
  (inputs [this] (underlying-set (source-object this)))
  (outputs [this] (underlying-set (target-object this)))

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(inputs this) (outputs this)]))

  clojure.lang.IFn
  (invoke [this [i v]]
    (cond
      (= i 0) (list 0 (afn v))
      (= i 1) (list 1 (bfn v))
      (= i 2) (list 2 (cfn v))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MorphismOfCospans :locus.base.logic.structure.protocols/structured-function)

; Component functions
(defn first-cospan-source-function
  [^MorphismOfCospans morphism]

  (->SetFunction
    (first-cospan-source (source-object morphism))
    (first-cospan-source (target-object morphism))
    (.-afn morphism)))

(defn second-cospan-source-function
  [^MorphismOfCospans morphism]

  (->SetFunction
    (second-cospan-source (source-object morphism))
    (second-cospan-source (target-object morphism))
    (.-bfn morphism)))

(defn cospan-target-function
  [^MorphismOfCospans morphism]

  (->SetFunction
    (cospan-target (source-object morphism))
    (cospan-target (target-object morphism))
    (.-cfn morphism)))

; Composition and identities in the topos of cospan copresheaves
(defmethod compose* MorphismOfCospans
  [^MorphismOfCospans a, ^MorphismOfCospans b]

  (MorphismOfCospans.
    (source-object b)
    (target-object a)
    (comp (.afn a) (.afn b))
    (comp (.bfn a) (.bfn b))
    (comp (.cfn a) (.cfn b))))

(defmethod identity-morphism Cospan
  [^Cospan cospan]

  (MorphismOfCospans.
    cospan
    cospan
    (identity-function (first-cospan-source cospan))
    (identity-function (second-cospan-source cospan))
    (identity-function (cospan-target cospan))))

; Products and coproducts in the topos Sets^{[1,1] x [2,1]}
(defmethod product MorphismOfCospans
  [& args]

  (->MorphismOfCospans
    (apply product (map source-object args))
    (apply product (map target-object args))
    (apply product (map first-cospan-source-function args))
    (apply product (map second-cospan-source-function args))
    (apply product (map cospan-target-function args))))

(defmethod coproduct MorphismOfCospans
  [& args]

  (->MorphismOfCospans
    (apply coproduct (map source-object args))
    (apply coproduct (map target-object args))
    (apply coproduct (map first-cospan-source-function args))
    (apply coproduct (map second-cospan-source-function args))
    (apply coproduct (map cospan-target-function args))))

; Subobject classifiers in the topos Sets^{[2,1]}
(def truth-cospan
  (cospan
    (mapfn {0 0, 1/2 1, 1 1})
    (mapfn {0 0, 1/2 1, 1 1})))

(defn subcospan-character
  [cospan new-first-source new-second-source new-target]

  (MorphismOfCospans.
    cospan
    truth-cospan
    (fn [first-source-element]
      (cond
        (contains? new-first-source first-source-element) 1
        (contains? new-target (apply-first-cospan-function cospan first-source-element)) 1/2
        :else 0))
    (fn [second-source-element]
      (cond
        (contains? new-second-source second-source-element) 1
        (contains? new-target (apply-second-cospan-function cospan second-source-element)) 1/2
        :else 0))
    (fn [target-element]
      (cond
        (contains? new-target target-element) 1
        :else 0))))

; Ontology of morphisms of cospans
(defn morphism-of-cospans?
  [cospan]

  (= (type cospan) MorphismOfCospans))

; Visualisation of morphisms of cospans
(defmethod visualize MorphismOfCospans
  [^MorphismOfCospans morphism]

  (let [first-cospan (source-object morphism)
        second-cospan (target-object morphism)
        [p t] (generate-copresheaf-data
                {0 (first-cospan-source first-cospan)
                 1 (second-cospan-source first-cospan)
                 2 (cospan-target first-cospan)

                 3 (first-cospan-source second-cospan)
                 4 (second-cospan-source second-cospan)
                 5 (cospan-target second-cospan)}
                #{(list 0 2 (first-cospan-function first-cospan))
                  (list 1 2 (second-cospan-function first-cospan))
                  (list 3 5 (first-cospan-function second-cospan))
                  (list 4 5 (second-cospan-function second-cospan))

                  (list 0 3 (first-cospan-source-function morphism))
                  (list 1 4 (second-cospan-source-function morphism))
                  (list 2 5 (cospan-target-function morphism))})]
    (visualize-clustered-digraph* "BT" p t)))