(ns locus.elementary.nary-quiver.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.partition.core.object :refer [projection]]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.ternary-quiver.core.object :refer :all]))

; A nary quiver is a family of parallel functions in the topos Sets. It is an object of the
; copresheaf topos of the category consisting of two objects and a series of parallel edges.
; As a family of copresheaves over various topoi, it generalizes various familiar constructions
; of topos theory like pairs of sets, functions, quivers, and ternary quivers. In the topos
; theoretic foundations of algebra, nary quivers are the most basic building block. As
; objects of a topos, all important constructs are generalized to deal with nary quivers
; such as the formation of subobject and congruence lattices.

(deftype NaryQuiver [edges vertices nth-component arity]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(first-set this) (second-set this)])))

(derive NaryQuiver :locus.elementary.copresheaf.core.protocols/structured-diset)

; This method computes the arity of a nary quiver. This can be used to determine the exact presheaf
; topos that a given nary quiver belongs to.
(defmethod quiver-arity NaryQuiver
  [^NaryQuiver quiver] (.-arity quiver))

; Get the nth component of n edge of an nary quiver
(defmulti nth-component (fn [a b c] (type a)))

(defmethod nth-component :locus.base.logic.structure.protocols/set-function
  [func edge i]

  (func i))

(defmethod nth-component :locus.elementary.quiver.core.object/quiver
  [quiver edge i]

  (case i
    0 (source-element quiver edge)
    1 (target-element quiver edge)))

(defmethod nth-component :locus.elementary.copresheaf.core.protocols/ternary-quiver
  [quiver edge i]

  (case i
    0 (first-component quiver edge)
    1 (second-component quiver edge)
    2 (third-component quiver edge)))

(defmethod nth-component NaryQuiver
  [^NaryQuiver quiver, edge, i]

  ((.-nth_component quiver) edge i))

; A nary quiver is a copresheaf and if it is of arity n then it has n different non-identity
; morphisms, each of which can be defined by the nth component function. These functions
; allow us to treat nary quivers as copresheaves over an appropriate parallel arrows category.
(defn nth-component-function
  [quiver i]

  (->SetFunction
    (morphisms quiver)
    (objects quiver)
    (fn [morphism]
      (nth-component quiver morphism i))))

; Every copresheaf is defined get-set and get-function methods.
(defmethod get-set NaryQuiver
  [^NaryQuiver quiver, i]

  (case i
    0 (first-set quiver)
    1 (second-set quiver)))

(defmethod get-function NaryQuiver
  [^NaryQuiver quiver, i]

  (cond
    (= i 0) (identity-function (first-set quiver))
    (= i 1) (identity-function (second-set quiver))
    :else (let [j (- i 2)]
            (nth-component-function quiver j))))

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

; An nary quiver of a chosen arity without any edges
(defn empty-nary-quiver
  [coll n]

  (->NaryQuiver #{} coll nth n))

; Singular nary quivers are essentially nary quivers with no more then one object
(defn singular-nary-quiver
  [coll obj n]

  (->NaryQuiver
    coll
    #{obj}
    (fn [edge i]
      obj)
    n))

; A coreflexive nary quiver is a nary quiver in which each nth component function is equal
(defn coreflexive-nary-quiver
  [func n]

  (->NaryQuiver
    (inputs func)
    (outputs func)
    (fn [edge i]
      (func edge))
    n))

; Create a nary quiver using a nary relation as a basis
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

(defmethod to-nary-quiver :locus.elementary.copresheaf.core.protocols/diset
  [diset]

  (->NaryQuiver
    (first-set diset)
    (second-set diset)
    nth
    0))

(defmethod to-nary-quiver :locus.base.logic.structure.protocols/set-function
  [func]

  (->NaryQuiver
    (inputs func)
    (outputs func)
    (fn [edge i]
      (func edge))
    1))

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

; The projection operation on nary quivers restricts the nary quiver to a set of slots
(defn nary-quiver-projection
  [quiver slots]

  (->NaryQuiver
    (morphisms quiver)
    (objects quiver)
    (fn [morphism i]
      (nth-component morphism (nth slots i)))
    (count slots)))

; Hom classes generalized to the nary case
(defn nary-quiver-hom-class
  [quiver coll]

  (set
    (filter
      (fn [morphism]
        (= (morphism-components quiver morphism) coll))
      (morphisms quiver))))

(defn nary-quiver-hom-class-cardinality
  [quiver coll]

  (count (nary-quiver-hom-class quiver coll)))

; Products and coproducts in topoi of nary quivers
(defn nary-quiver-product
  [& quivers]

  (->NaryQuiver
    (apply product (map first-set quivers))
    (apply product (map second-set quivers))
    (fn [edge index]
      (map-indexed
        (fn [i v]
          (nth-component (nth quivers i) v index))
        edge))
    (quiver-arity (first quivers))))

(defn nary-quiver-coproduct
  [& quivers]

  (->NaryQuiver
    (apply coproduct (map first-set quivers))
    (apply coproduct (map second-set quivers))
    (fn [[tag val] index]
      (list tag (nth-component (nth quivers index) val index)))
    (quiver-arity (first quivers))))

(defmethod product NaryQuiver
  [& quivers]

  (apply nary-quiver-product quivers))

(defmethod coproduct NaryQuiver
  [& quivers]

  (apply nary-quiver-coproduct quivers))

; Images and inverse of nary quivers
(defn nary-quiver-set-image
  [quiver morphisms]

  (apply
    union
    (map
      (fn [morphism]
        (set (morphism-components quiver morphism)))
      morphisms)))

(defn nary-quiver-inverse-set-image
  [quiver objects]

  (set
    (filter
      (fn [morphism]
        (superset? (list (set (morphism-components quiver morphism)) objects)))
      (morphisms quiver))))

(defn nary-quiver-partition-image
  [quiver in-partition]

  (apply
    join-set-partitions
    (map
      (fn [i]
        (partition-image (nth-component-function quiver i) in-partition))
      (range (quiver-arity quiver)))))

(defn ternary-quiver-partition-inverse-image
  [quiver out-partition]

  (apply
    meet-set-partitions
    (map
      (fn [i]
        (partition-inverse-image (nth-component-function quiver i) out-partition))
      (range (quiver-arity quiver)))))

; Ontology of nary quivers
(defn nary-quiver?
  [obj]

  (= (type obj) NaryQuiver))

(defn thin-nary-quiver?
  [quiver]

  (and
    (nary-quiver? quiver)
    (universal? (underlying-multirelation quiver))))

