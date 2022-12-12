(ns locus.con.mapping.function
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.object :refer :all]
            [dorothy.core :as dot]))

; Function congruences are also presheaves of equivalence relations. In fact, for any presheaf
; its congruence lattice is the same as its lattice of structure presheaves of equivalence
; relations. In this sense, we generalize this concept in a presheaf-theoretic formalism
; to congruences of presheaves over arbitrary categories.
(deftype FunctionCongruence [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this obj] (func obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive FunctionCongruence :locus.set.logic.structure.protocols/structured-function)

; Get the equivalence relations of the function congruence as a presheaf of equivalence relations
(defn input-equivalence-classes
  [function-congruence]

  (equivalence-classes (source-object function-congruence)))

(defn output-equivalence-classes
  [function-congruence]

  (equivalence-classes (target-object function-congruence)))

; A constructor for function congruences
(defn function-congruence
  [func in-partition out-partition]

  (->FunctionCongruence
    in-partition
    out-partition
    func))

; Get the injective closure of a function congruence
(defn injective-function-congruence-closure
  [function-congruence]

  (let [func (underlying-function function-congruence)
        out-partition (target-object function-congruence)]
    (->FunctionCongruence
      (->SetPartition (partition-inverse-image func (equivalence-classes out-partition)))
      out-partition
      func)))

; Get a quotient function by a function congruence
(defmethod get-quotient FunctionCongruence
  [function-congruence]

  (quotient-function
    (underlying-function function-congruence)
    (input-equivalence-classes function-congruence)
    (output-equivalence-classes function-congruence)))

; Functions are canonically function congruences by the trivial partition
(defmulti to-function-congruence type)

(defmethod to-function-congruence FunctionCongruence
  [function-congruence] function-congruence)

(defmethod to-function-congruence :locus.set.logic.structure.protocols/set-function
  [func]

  (->FunctionCongruence
    (->SetPartition (set (map (fn [i] #{i}) (inputs func))))
    (->SetPartition (set (map (fn [i] #{i}) (outputs func))))
    func))

; Products and coproducts of function congruences
(defmethod coproduct FunctionCongruence
  [& functions]

  (->FunctionCongruence
    (->CoproductPartition [(map source-object functions)])
    (->CoproductPartition [(map target-object functions)])
    (fn [[i v]]
      (list i ((nth functions i) v)))))

(defmethod product FunctionCongruence
  [& functions]

  (->FunctionCongruence
    (->ProductPartition [(map source-object functions)])
    (->ProductPartition [(map target-object functions)])
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth functions i) v))
        coll))))

; Ontology of function congruences as special types of presheaves of equivalence relations
(defn set-function-congruence?
  [obj]

  (= (type obj) FunctionCongruence))

; This visualises function congruences using graphviz routines
(defmethod visualize FunctionCongruence
  [function-congruence]

  (let [in-family (equivalence-classes (source-object function-congruence))
        in-coll (vec (seq (apply union in-family)))
        out-family (equivalence-classes (target-object function-congruence))
        out-coll (vec (seq (apply union out-family)))
        in-labeling (map
                      (fn [coll]
                        (into
                          {}
                          (map
                           (fn [elem]
                             [(.indexOf in-coll elem) elem])
                           coll)))
                      in-family)
        out-labeling (map
                       (fn [coll]
                         (into
                           {}
                           (map
                             (fn [elem]
                               [(+ (count in-coll) (.indexOf out-coll elem)) elem])
                             coll)))
                       out-family)]
    (output-graph!
      (dot/dot
        (dot/digraph
          [{:rankdir "LR"}
           (create-clustered-equivalence-relation-digraph* "cluster_a" in-labeling)
           (create-clustered-equivalence-relation-digraph* "cluster_b" out-labeling)
           (map
             (fn [in]
               (let [out (function-congruence in)]
                 [(str (.indexOf in-coll in))
                  (str (+ (count in-coll) (.indexOf out-coll out)))]))
             (inputs function-congruence))])))))