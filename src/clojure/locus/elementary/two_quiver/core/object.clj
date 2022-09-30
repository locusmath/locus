(ns locus.elementary.two-quiver.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.quiver.core.object :refer :all])
  (:import (locus.elementary.quiver.core.object Quiver)))

; A 2-quiver is defined by an ordered pair of quivers P,Q : A -> B -> C, in which the two
; quivers are composable so that the morphism set of one quiver is equal to the object
; set of another. This is similar to how given a pair of function f: A -> B and
; g: B -> C sharing a common input and output, they can form a triangle copresheaf. So
; these include any pair of quivers that can be chained together, without extra conditions.
; Special cases include path quivers and two globular sets.
(defprotocol StructuredTwoQuiver
  "A general protocol for describing structures over two-quiver copresheaves."

  (two-morphisms [this]
    "The two morphisms of the structured quiver.")
  (two-source-fn [this]
    "The source morphism of a two morphism in a two globular set.")
  (two-target-fn [this]
    "The target morphism of a two morphism in a two globular set."))

(deftype TwoQuiver [two-morphisms morphisms objects two-source two-target source target]
  StructuredDiset
  (first-set [this] objects)
  (second-set [this] morphisms)

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [two-morphisms morphisms objects]))

  StructuredQuiver
  (underlying-quiver [this]
    (->Quiver
      morphisms
      objects
      source
      target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e]
    (list (source e) (target e)))

  StructuredTwoQuiver
  (two-morphisms [this] two-morphisms)
  (two-source-fn [this] two-source)
  (two-target-fn [this] two-target))

(derive TwoQuiver :locus.elementary.copresheaf.core.protocols/structured-quiver)

(defmethod visualize TwoQuiver
  [quiver]

  (visualize (underlying-quiver quiver)))

; Underlying relations and multirelations
(defmethod underlying-relation TwoQuiver
  [quiver]

  (underlying-relation (underlying-quiver quiver)))

; The special case of underlying multirelations of two quivers
(defmethod underlying-multirelation TwoQuiver
  [quiver]

  (underlying-multirelation (underlying-quiver quiver)))

; Component functions for 2-morphisms in 2-quivers
(defn two-morphism-s
  [quiver two-morphism]

  ((two-source-fn quiver) two-morphism))

(defn two-morphism-t
  [quiver two-morphism]

  ((two-target-fn quiver) two-morphism))

(defn two-morphism-ss
  [quiver two-morphism]

  (source-element quiver (two-morphism-s quiver two-morphism)))

(defn two-morphism-st
  [quiver two-morphism]

  (source-element quiver (two-morphism-t quiver two-morphism)))

(defn two-morphism-ts
  [quiver two-morphism]

  (target-element quiver (two-morphism-s quiver two-morphism)))

(defn two-morphism-tt
  [quiver two-morphism]

  (target-element quiver (two-morphism-t quiver two-morphism)))

; Corresponding morphisms for the component functions
(defn s-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (morphisms quiver)
    (fn [two-morphism]
      (two-morphism-s quiver two-morphism))))

(defn t-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (morphisms quiver)
    (fn [two-morphism]
      (two-morphism-t quiver two-morphism))))

(defn ss-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (objects quiver)
    (fn [two-morphism]
      (two-morphism-ss quiver two-morphism))))

(defn st-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (objects quiver)
    (fn [two-morphism]
      (two-morphism-st quiver two-morphism))))

(defn ts-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (objects quiver)
    (fn [two-morphism]
      (two-morphism-ts quiver two-morphism))))

(defn tt-function
  [quiver]

  (->SetFunction
    (two-morphisms quiver)
    (objects quiver)
    (fn [two-morphism]
      (two-morphism-tt quiver two-morphism))))

; The morphic quiver of a two quiver copresheaf
(defn morphic-quiver
  [quiver]

  (->Quiver
    (two-morphisms quiver)
    (morphisms quiver)
    (two-source-fn quiver)
    (two-target-fn quiver)))

; Combine two quivers in order to create a 2-quiver copresheaf
(defn combine-quivers
  [morphic-quiver object-quiver]

  (->TwoQuiver
    (morphisms morphic-quiver)
    (morphisms object-quiver)
    (objects object-quiver)
    (source-fn morphic-quiver)
    (target-fn morphic-quiver)
    (source-fn object-quiver)
    (target-fn object-quiver)))

; Create a two quiver with a single object, but any number of morphisms or two morphisms. These type
; of structures include monoidal categories and a number of other constructions like ordered
; monoids and semigroups, which enrich a singular quiver with an ordering on morphisms.
(defn singular-two-quiver
  [quiver object]

  (combine-quivers
    quiver
    (singular-quiver (morphisms quiver) object)))

; A quiver with no two-morphisms
(defn two-morphism-free-quiver
  [quiver]

  (combine-quivers
    (->Quiver #{} (morphisms quiver) first second)
    quiver))

; A relational two-quiver is actually formed from a binary relation on ordered pairs, so each
; element of the component binary relation should be of the form ((a b) (c d)). This makes
; for a much nicer relational two quiver then having to use a quaternary relation, in
; which case the component edges would have to be produced differently.
(defn relational-two-quiver
  [rel]

  (let [objects (apply union (map (fn [[a b] [c d]] (set (list a b c d))) rel))
        morphisms (apply union (map set rel))]
    (->TwoQuiver
      rel
      morphisms
      objects
      first
      second
      first
      second)))

; Create a composability two-quiver from a quiver
(defn composability-two-quiver
  [quiver]

  (combine-quivers
    (composability-quiver quiver)
    quiver))

; Create a parallelism two quiver from a quiver. This is like a two globular set within the
; ontology of two quivers.
(defn parallelism-two-quiver
  [quiver]

  (combine-quivers
    (parallelism-quiver quiver)
    quiver))

;  Convert structures into two quivers
(defmulti to-two-quiver type)

(defmethod to-two-quiver TwoQuiver
  [two-quiver] two-quiver)

(defmethod to-two-quiver Quiver
  [quiver] (two-morphism-free-quiver quiver))

; Products and coproducts in the topos of two-quivers
(defn two-quiver-product
  [& quivers]

  (->TwoQuiver
    (apply cartesian-product (map two-morphisms quivers))
    (apply cartesian-product (map morphisms quivers))
    (apply cartesian-product (map objects quivers))
    (apply product (map s-function quivers))
    (apply product (map t-function quivers))
    (apply product (map source-function quivers))
    (apply product (map target-function quivers))))

(defn two-quiver-coproduct
  [& quivers]

  (->TwoQuiver
    (apply cartesian-coproduct (map two-morphisms quivers))
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (apply coproduct (map s-function quivers))
    (apply coproduct (map t-function quivers))
    (apply coproduct (map source-function quivers))
    (apply coproduct (map target-function quivers))))

(defmethod product TwoQuiver
  [& quivers]

  (apply two-quiver-product quivers))

(defmethod coproduct TwoQuiver
  [& quivers]

  (apply two-quiver-coproduct quivers))

; The ontology of sub two quivers
(defn sub-two-quiver?
  [quiver new-two-morphisms new-morphisms new-objects]

  (and
    (superset?
      (list
        (union
          (set-image (source-function quiver) new-morphisms)
          (set-image (target-function quiver) new-morphisms))
        new-objects))
    (superset?
      (list
        (union
          (set-image (s-function quiver) new-two-morphisms)
          (set-image (s-function quiver) new-two-morphisms))
        new-morphisms))))

(defn two-quiver-congruence?
  [quiver two-congruence one-congruence zero-congruence]

  (and
    (io-relation? (source-function quiver) one-congruence zero-congruence)
    (io-relation? (target-function quiver) one-congruence zero-congruence)
    (io-relation? (s-function quiver) two-congruence one-congruence)
    (io-relation? (t-function quiver) two-congruence one-congruence)))

; Restrict the two morphisms of a two quiver
(defn restrict-two-morphisms
  [two-quiver new-two-morphisms]

  (->TwoQuiver
    new-two-morphisms
    (morphisms two-quiver)
    (objects two-quiver)
    (two-source-fn two-quiver)
    (two-target-fn two-quiver)
    (source-fn two-quiver)
    (target-fn two-quiver)))

(defn globular-two-morphism?
  [two-quiver two-morphism]

  (let [source (two-morphism-s two-quiver two-morphism)
        target (two-morphism-t two-quiver two-morphism)]
    (parallel-elements? two-quiver source target)))

(defn globular-two-morphisms
  [two-quiver]

  (set
    (filter
      (fn [two-morphism]
        (globular-two-morphism? two-quiver two-morphism))
      (two-morphisms two-quiver))))

(defn globular-component
  [two-quiver]

  (restrict-two-morphisms two-quiver (globular-two-morphisms two-quiver)))

; Ontology of two quivers
(defn two-quiver?
  [two-quiver]

  (= (type two-quiver) TwoQuiver))

(defn globular-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (every?
      (fn [morphism]
        (globular-two-morphism? two-quiver morphism))
      (two-morphisms two-quiver))))

