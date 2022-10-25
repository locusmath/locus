(ns locus.elementary.dependency.chain.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all]
            [locus.elementary.dependency.chain.object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.dependency.chain.object ChainCopresheaf)))

; Let Sets^{T_n} be the topos of copresheaves over a total order T_n. Then a morphism in this
; topos is called a morphism of chains. This file exists to support the implementation
; of methods related to objects of this topos. In particular, morphisms in Sets^{T_n} are
; themselves treated as types of presheaves in the topos Sets^{T_2 x T_n} so that they
; have all attendant presheaf-theoretic properties and functionality associated with
; them such as products, coproducts, subobjects, quotients, and so on.

(deftype ChainMorphism [source-chain target-chain funcs]
  AbstractMorphism
  (source-object [this]
    source-chain)
  (target-object [this]
    target-chain))

; Component functions of a morphism of chain copresheaves
(defn chain-morphism-component-function
  [^ChainMorphism morphism, i]

  (->SetFunction
    (nth-set-from-source (source-object morphism) i)
    (nth-set-from-source (target-object morphism) i)
    (nth (.-funcs morphism) i)))

; Components of morphisms of chain copresheaves
(defmethod get-set ChainMorphism
  [morphism [i v]]

  (case i
    0 (get-set (source-object morphism) v)
    1 (get-set (target-object morphism) v)))

(defmethod get-function ChainMorphism
  [morphism [[i v] [j w]]]

  (case [i j]
    [0 0] (get-function (source-object morphism) [v w])
    [1 1] (get-function (target-object morphism) [v w])
    [0 1] (compose
            (get-function (target-object morphism) [v w])
            (chain-morphism-component-function morphism v))))

; Composition and identities in the topos of chain copresheaves
(defmethod compose* ChainMorphism
  [^ChainMorphism a, ^ChainMorphism b]

  (let [n (count (.-funcs a))]
    (ChainMorphism.
      (source-object b)
      (target-object a)
      (map
        (fn [i]
          (compose (nth (.-funcs a) i) (nth (.-funcs b) i)))
        (range n)))))

(defmethod identity-morphism ChainCopresheaf
  [^ChainCopresheaf chain]

  (->ChainMorphism
    chain
    chain
    (set-sequence-from-source chain)))

; Products and coproducts in topoi of chain copresheaves
(defmethod product ChainMorphism
  [& args]

  (let [n (inc (count (composition-sequence (first args))))]
    (->ChainMorphism
      (apply product (map source-object args))
      (apply product (map target-object args))
      (map
        (fn [i]
          (apply
            product
            (map
              (fn [arg]
                (chain-morphism-component-function arg i))
              args)))
        (range n)))))

(defmethod coproduct ChainMorphism
  [& args]

  (let [n (inc (count (composition-sequence (first args))))]
    (->ChainMorphism
      (apply coproduct (map source-object args))
      (apply coproduct (map target-object args))
      (map
        (fn [i]
          (apply
            coproduct
            (map
              (fn [arg]
                (chain-morphism-component-function arg i))
              args)))
        (range n)))))

; Ontology of morphisms in the topos of chain copresheaves
(defn morphism-of-chains?
  [morphism]

  (= (type morphism) ChainMorphism))
