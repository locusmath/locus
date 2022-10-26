(ns locus.elementary.dependency.chain.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.function.core.util :refer :all])
  (:import (locus.base.function.core.object SetFunction)))

; Objects of a copresheaf Sets^{T_n} are called chain copresheaves. Their underlying index
; categories are the finite total orders. The triangle copresheaves, which consist of
; ordered pairs of composable functions are a special case. In more advanced applications,
; it is common to deal with chain copresheaves with additional structure. In this
; file we will simply focus on the elementary topos theoretic aspects of copresheaves
; over finite chain total orders.
(deftype SetChain [functions])

; Get an nth set starting from the source
(defn composition-sequence
  [^SetChain chain]

  (.-functions chain))

(defn nth-set-from-source
  [chain i]

  (let [reverse-functions (reverse (composition-sequence chain))]
    (if (zero? i)
      (inputs (first reverse-functions))
      (outputs (nth reverse-functions (dec i))))))

(defn set-sequence-from-source
  [chain]

  (let [functions (reverse (composition-sequence chain))]
    (concat
      (map inputs functions)
      (list (outputs (last functions))))))

(defn get-function-at-nth-point-from-source
  [chain i]

  (let [functions (composition-sequence chain)
        last-index (dec (count functions))]
    (nth functions (- last-index i))))

(defn get-chain-transition-function
  [chain x y]

  (if (= x y)
    (identity-function (nth-set-from-source chain x))
    (apply
      compose
      (map
        (fn [i]
          (get-function-at-nth-point-from-source chain i))
        (reverse (range x y))))))

(defmethod get-set SetChain
  [^SetChain chain, i]

  (nth-set-from-source chain i))

(defmethod get-function SetChain
  [^SetChain chain, [a b]]

  (get-chain-transition-function chain a b))

; Get the parent topos of a chain copresheaf
(defn chain-type
  [^SetChain chain]

  (count (composition-sequence chain)))

; Get the composition of a chain copresheaf
(defn chain-composition
  [^SetChain chain]

  (apply compose (composition-sequence chain)))

; Compose components in the chain copresheaf
(defn compose-components
  [chain i]

  (let [j (inc i)
        functions (composition-sequence chain)]
    (->SetChain
      (concat
        (take i functions)
        (list (compose (nth functions j) (nth functions i)))
        (drop (inc j) functions)))))

(defn adjoin-identity-function
  [chain i]

  (let [functions (composition-sequence chain)
        n (count functions)]
    (->SetChain
      (concat
        (take i functions)
        (let [coll (if (= n i)
                     (inputs (last functions))
                     (outputs (nth functions i)))]
          (list (identity-function coll)))
        (drop i functions)))))

; Eliminate identity functions from a chain copresheaf
(defn eliminate-identity-functions
  [chain]

  (->SetChain
    (filter
      (fn [function]
        (not (identity-function? function)))
      (composition-sequence chain))))

; Conversion multimethods
(defmulti to-set-chain type)

(defmethod to-set-chain SetChain
  [^SetChain chain] chain)

(defmethod to-set-chain SetFunction
  [^SetFunction func] (->SetChain [func]))

(defn singleton-chain
  [& coll]

  (SetChain.
    (reverse
      (map
        (fn [i]
          (pair-function (nth coll i) (nth coll (inc i))))
        (range (dec (count coll)))))))

(defmethod to-set-chain clojure.lang.ISeq
  [coll] (apply singleton-chain coll))

(defmethod to-set-chain clojure.lang.IPersistentVector
  [coll] (apply singleton-chain coll))

; Create an inclusion chain from a monotone sequence of sets
(defn inclusion-chain
  [coll]

  (SetChain.
    (reverse
      (map
        (fn [i]
          (inclusion-function (nth coll i) (nth coll (inc i))))
        (range (dec (count coll)))))))

; Products and coproducts in topoi of chain copresheaves
(defmethod product SetChain
  [& chains]

  (let [n (chain-type (first chains))]
    (SetChain.
      (map
        (fn [i]
          (apply
            function-product
            (map
              (fn [chain]
                (nth (composition-sequence chain) i))
              chains)))
        (range n)))))

(defmethod coproduct SetChain
  [& chains]

  (let [n (chain-type (first chains))]
    (SetChain.
      (map
        (fn [i]
          (apply
            function-coproduct
            (map
              (fn [chain]
                (nth (composition-sequence chain) i))
              chains)))
        (range n)))))

; Ontology of chain copresheaves
(defn set-chain?
  [chain]

  (= (type chain) SetChain))

(defn chain-of-injective-functions?
  [chain]

  (and
    (set-chain? chain)
    (every? injective? (composition-sequence chain))))

(defn chain-of-surjective-functions?
  [chain]

  (and
    (set-chain? chain)
    (every? surjective? (composition-sequence chain))))

(defn chain-of-invertible-functions?
  [chain]

  (and
    (set-chain? chain)
    (every? invertible? (composition-sequence chain))))

(defn identity-free-chain?
  [chain]

  (and
    (set-chain? chain)
    (every?
      (fn [i]
        (not (identity-function? i)))
      (composition-sequence chain))))

; Create the data for a chain copresheaf
(defn create-chain-data
  [args]

  (let [functions (reverse args)
        colls (vec
                (concat
                  (map inputs functions)
                  (list (outputs (last functions)))))
        triples (map-indexed
                  (fn [i function]
                    (list i (inc i) function))
                  functions)]
    (list (vector->map colls) triples)))

(defmethod visualize SetChain
  [^SetChain chain]

  (let [[p t] (apply
                generate-copresheaf-data
                (create-chain-data (composition-sequence chain)))]
    (visualize-clustered-digraph* "LR" p t)))

