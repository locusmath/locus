(ns locus.elementary.nary-quiver.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]))

; An Nary-Quiver is a family of parallel functions in the topos Sets. It is an object of the copresheaf
; topos of the category consisting of two objects and a series of parallel edges.
(deftype NaryQuiver [edges vertices nth-component arity]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(first-set this) (second-set this)])))

(derive NaryQuiver :locus.elementary.copresheaf.core.protocols/structured-diset)

; Get the arity of a quiver
(defmulti quiver-arity type)

(defmethod quiver-arity NaryQuiver
  [^NaryQuiver quiver] (.-arity quiver))

(defmethod quiver-arity :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiver] 3)

(defmethod quiver-arity :locus.elementary.quiver.core.object/quiver
  [quiver] 2)

; Get the nth component of n edge of an nary quiver
(defmulti nth-component (fn [a b c] (type a)))

(defmethod nth-component NaryQuiver
  [^NaryQuiver quiver, edge, i]

  ((.-nth_component quiver) edge i))

; Get all the components of a morphism
(defn morphism-components
  [quiver morphism]

  (map
    (fn [i]
      (nth-component quiver morphism i))
    (range (quiver-arity quiver))))

; Relational aspects of nary quivers
(defmethod underlying-multirelation NaryQuiver
  [^NaryQuiver quiver]

  (set
    (map
      (fn [morphism]
        (morphism-components quiver morphism))
      (morphisms quiver))))

(defmethod underlying-relation NaryQuiver
  [^NaryQuiver quiver]

  (set (underlying-multirelation quiver)))

; Create a nary quiver using an nary relation as a basis
(defn relational-nary-quiver
  ([edges]
   (relational-nary-quiver (vertices edges) edges (count (first edges))))
  ([vertices edges]
   (relational-nary-quiver vertices edges (count (first edges))))
  ([vertices edges n]
   (NaryQuiver. edges vertices nth n)))

; Conversion routines for nary quivers
(defmulti to-nary-quiver type)

(defmethod to-nary-quiver NaryQuiver
  [^NaryQuiver quiver] quiver)

(defmethod to-nary-quiver :locus.elementary.quiver.core.object/quiver
  [quiver]

  (->NaryQuiver
    (morphisms quiver)
    (objects quiver)
    (fn [edge i]
      (case i
        0 (source-element quiver edge)
        1 (target-element quiver edge)))
    2))

(defmethod to-nary-quiver :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiver]

  (->NaryQuiver
    (morphisms quiver)
    (objects quiver)
    (fn [edge i]
      (case i
        0 (first-component quiver edge)
        1 (second-component quiver edge)
        2 (third-component quiver edge)))
    3))

(defmethod to-nary-quiver :locus.base.logic.core.set/universal
  [coll]

  (relational-nary-quiver coll))

; Ontology of nary quivers
(defn nary-quiver?
  [obj]

  (= (type obj) NaryQuiver))