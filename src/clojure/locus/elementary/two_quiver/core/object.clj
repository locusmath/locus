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
            [locus.base.partition.core.object :refer [projection]]
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
  (first-set [this] morphisms)
  (second-set [this] objects)

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

; Components of two quivers
(defmethod get-set TwoQuiver
  [two-quiver x]

  (case x
    0 (objects two-quiver)
    1 (morphisms two-quiver)
    2 (two-morphisms two-quiver)))

(defmethod get-function TwoQuiver
  [two-quiver coll]

  (cond
    (= coll '(0 0 ())) (identity-function (objects two-quiver))
    (= coll '(1 0 (0))) (source-function two-quiver)
    (= coll '(1 0 (1))) (target-function two-quiver)
    (= coll '(1 1 ())) (identity-function (morphisms two-quiver))
    (= coll '(2 2 ())) (identity-function (two-morphisms two-quiver))
    (= coll '(2 1 (0))) (s-function two-quiver)
    (= coll '(2 1 (1))) (t-function two-quiver)
    (= coll '(2 0 (0 0))) (ss-function two-quiver)
    (= coll '(2 0 (0 1))) (st-function two-quiver)
    (= coll '(2 0 (1 0))) (ts-function two-quiver)
    (= coll '(2 0 (1 1))) (tt-function two-quiver)))

; All 2-morphisms between a pair of 1-morphisms
(defn two-hom
  [quiver a b]

  (set
    (filter
      (fn [two-morphism]
        (and
          (= (two-morphism-s quiver two-morphism) a)
          (= (two-morphism-t quiver two-morphism) b)))
      (two-morphisms quiver))))

; Underlying relations and multirelations
(defmethod underlying-relation TwoQuiver
  [quiver]

  (underlying-relation (underlying-quiver quiver)))

; The special case of underlying multirelations of two quivers
(defmethod underlying-multirelation TwoQuiver
  [quiver]

  (underlying-multirelation (underlying-quiver quiver)))

; The underlying multirelation of the morphic quiver
(defn underlying-two-multirelation
  [quiver]

  (multiset
    (map
      (fn [two-morphism]
        (list
          (two-morphism-s quiver two-morphism)
          (two-morphism-t quiver two-morphism)))
      (two-morphisms quiver))))

(defn underlying-two-relation
  [quiver]

  (set (underlying-two-multirelation quiver)))

; The morphic quiver of a two quiver copresheaf
; This contains one morphisms as its objects and two morphisms as its morphisms.
(defn morphic-quiver
  [quiver]

  (->Quiver
    (two-morphisms quiver)
    (morphisms quiver)
    (two-source-fn quiver)
    (two-target-fn quiver)))

; Combine two quivers in order to create a 2-quiver copresheaf
; This is similar to how two functions can be combined to create a triangle copreshaef
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

; Two quivers created from special types of quivers naturally associated with 1-quivers based upon
; various relations, including relations of composability, parallelism, source, and target equality.
(defn composability-two-quiver
  [quiver]

  (combine-quivers
    (composability-quiver quiver)
    quiver))

(defn parallelism-two-quiver
  [quiver]

  (combine-quivers
    (parallelism-quiver quiver)
    quiver))

(defn source-equivalence-two-quiver
  [quiver]

  (combine-quivers
    (source-equivalence-quiver quiver)
    quiver))

(defn target-equivalence-two-quiver
  [quiver]

  (combine-quivers
    (target-equivalence-quiver quiver)
    quiver))

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

;  Convert structures into two quivers
(defmulti to-two-quiver type)

(defmethod to-two-quiver TwoQuiver
  [two-quiver] two-quiver)

(defmethod to-two-quiver Quiver
  [quiver] (two-morphism-free-quiver quiver))

(defmethod to-two-quiver :locus.base.logic.core.set/universal
  [rel] (two-morphism-free-quiver (relational-quiver rel)))

; Products and coproducts in the topos of two-quivers
(defmethod product TwoQuiver
  [& quivers]

  (->TwoQuiver
    (apply cartesian-product (map two-morphisms quivers))
    (apply cartesian-product (map morphisms quivers))
    (apply cartesian-product (map objects quivers))
    (apply product (map s-function quivers))
    (apply product (map t-function quivers))
    (apply product (map source-function quivers))
    (apply product (map target-function quivers))))

(defmethod coproduct TwoQuiver
  [& quivers]

  (->TwoQuiver
    (apply cartesian-coproduct (map two-morphisms quivers))
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (apply coproduct (map s-function quivers))
    (apply coproduct (map t-function quivers))
    (apply coproduct (map source-function quivers))
    (apply coproduct (map target-function quivers))))

; Subobjects in the topos of 2-quivers
(defn two-subquiver?
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

(defn two-subquiver
  [quiver new-two-morphisms new-morphisms new-objects]

  (->TwoQuiver
    new-two-morphisms
    new-morphisms
    new-objects
    (two-source-fn quiver)
    (two-target-fn quiver)
    (source-fn quiver)
    (target-fn quiver)))

; Congruences of objects in the topos of 2-quivers
(defn two-quiver-congruence?
  [quiver two-congruence one-congruence zero-congruence]

  (and
    (io-relation? (source-function quiver) one-congruence zero-congruence)
    (io-relation? (target-function quiver) one-congruence zero-congruence)
    (io-relation? (s-function quiver) two-congruence one-congruence)
    (io-relation? (t-function quiver) two-congruence one-congruence)))

(defn two-quiver-quotient
  [quiver two-congruence one-congruence zero-congruence]

  (->TwoQuiver
    two-congruence
    one-congruence
    zero-congruence
    (fn [part]
      (projection one-congruence (two-morphism-s quiver (first part))))
    (fn [part]
      (projection one-congruence (two-morphism-t quiver (first part))))
    (fn [part]
      (projection zero-congruence (source-element quiver (first part))))
    (fn [part]
      (projection zero-congruence (target-element quiver (first part))))))

; Over quivers
(defn target-equal-two-morphism-components?
  [two-quiver two-morphism]

  (target-equal-elements?
    two-quiver
    (two-morphism-s two-quiver two-morphism)
    (two-morphism-t two-quiver two-morphism)))

(defn over-two-morphisms
  [two-quiver]

  (set
    (filter
      (partial target-equal-two-morphism-components? two-quiver)
      (two-morphisms two-quiver))))

(defn over-component
  [two-quiver]

  (restrict-two-morphisms two-quiver (over-two-morphisms two-quiver)))

; Under quivers
(defn source-equal-two-morphism-components?
  [two-quiver two-morphism]

  (source-equal-elements?
    two-quiver
    (two-morphism-s two-quiver two-morphism)
    (two-morphism-t two-quiver two-morphism)))

(defn under-two-morphisms
  [two-quiver]

  (set
    (filter
      (partial source-equal-two-morphism-components? two-quiver)
      (two-morphisms two-quiver))))

(defn under-component
  [two-quiver]

  (restrict-two-morphisms two-quiver (under-two-morphisms two-quiver)))

; Globular subobjects of two quivers
(defn globular-two-morphism?
  [two-quiver two-morphism]

  (let [source (two-morphism-s two-quiver two-morphism)
        target (two-morphism-t two-quiver two-morphism)]
    (parallel-elements? two-quiver source target)))

(defn globular-two-morphisms
  [two-quiver]

  (set
    (filter
      (partial globular-two-morphism? two-quiver)
      (two-morphisms two-quiver))))

(defn globular-component
  [two-quiver]

  (restrict-two-morphisms two-quiver (globular-two-morphisms two-quiver)))

; Ontology of two quivers
(defn two-quiver?
  [two-quiver]

  (= (type two-quiver) TwoQuiver))

(defn over-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (every?
      (fn [morphism]
        (target-equal-two-morphism-components? two-quiver morphism))
      (two-morphisms two-quiver))))

(defn under-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (every?
      (fn [morphism]
        (source-equal-two-morphism-components? two-quiver morphism))
      (two-morphisms two-quiver))))

(defn globular-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (every?
      (fn [morphism]
        (globular-two-morphism? two-quiver morphism))
      (two-morphisms two-quiver))))

(defn one-thin-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (universal? (underlying-multirelation two-quiver))))

(defn two-thin-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (universal? (underlying-two-multirelation two-quiver))))

(defn dually-thin-two-quiver?
  [two-quiver]

  (and
    (two-quiver? two-quiver)
    (universal? (underlying-multirelation two-quiver))
    (universal? (underlying-two-multirelation two-quiver))))
