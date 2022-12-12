(ns locus.hyper.quiver.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.nary.core.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.hyper.mapping.function :refer :all])
  (:import (locus.hyper.mapping.function Hyperfunction)
           (locus.set.quiver.nary.core.object NaryQuiver)
           (locus.set.quiver.diset.core.object Diset)
           (locus.set.mapping.general.core.object SetFunction)))

; A hyperquiver is a functor from F: T_{2,n} -> Rel from the parallel arrows category T_{2,n} to
; the concrete category of sets and multivalued functions. Hyperquivers are one of the most
; basic examples of hypercopresheaves, which are functors to the allegory Rel of sets and
; multivalued functions. Hyperquivers are implemented as part of the Locus structure
; copresheaf framework, which lets structure copresheaves be treated as like functors and
; copresheaves at the same time.

; One possible interpretation of hyperquivers is that they are like a set of vertices
; with a set of edges where the source, target, and other components of the edges can
; have multiple vertices. So a hyperedge in a hyperquiver can have any number of source or
; target vertices. In accordance with this interpretation, we provide the underlying multirelation
; function which turns a nary hyperquiver into a set of lists of sets.
(deftype NaryHyperquiver [edges vertices nth-component arity]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices))

(derive NaryHyperquiver :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Compute the arities of hyperquivers
(defmulti hyperquiver-arity type)

(defmethod hyperquiver-arity NaryHyperquiver
  [^NaryHyperquiver hyperquiver]

  (.-arity hyperquiver))

; Get the components of a hyperedge
(defn nth-hypercomponent
  [^NaryHyperquiver quiver, edge, i]

  ((.-nth_component quiver) edge i))

(defn morphism-hypercomponents
  [^NaryHyperquiver quiver, edge]

  (map
    (fn [i]
      (nth-hypercomponent quiver edge i))
    (range (hyperquiver-arity quiver))))

; The hyperfunctions of the hyperquiver as a hypercopresheaf
(defn nth-component-hyperfunction
  [hyperquiver i]

  (->Hyperfunction
    (morphisms hyperquiver)
    (objects hyperquiver)
    (fn [edge]
      (nth-hypercomponent hyperquiver edge i))))

; Methods to include nary hyperquivers in the structure copresheaves framework
(defmethod get-object NaryHyperquiver
  [hyperquiver i]

  (case i
    0 (morphisms hyperquiver)
    1 (objects hyperquiver)))

(defmethod get-morphism NaryHyperquiver
  [hyperquiver i]

  (cond
    (zero? i) (identity-hyperfunction (morphisms hyperquiver))
    (= i 1) (identity-hyperfunction (objects hyperquiver))
    :else (nth-component-hyperfunction hyperquiver (- i 2))))

(defmethod get-set NaryHyperquiver
  [hyperquiver i]

  (->PowerSet (get-object hyperquiver i)))

(defmethod get-function NaryHyperquiver
  [hyperquiver i]

  (to-function (get-morphism hyperquiver i)))

; As nary quivers are structure copresheaves, it is reasonable to suppose that they have underlying
; copresheaves. These can acquired by using the to-nary-quiver multimethod.
(defmethod to-nary-quiver NaryHyperquiver
  [^NaryHyperquiver hyperquiver]

  (->NaryQuiver
    (->PowerSet (morphisms hyperquiver))
    (->PowerSet (objects hyperquiver))
    (fn [edge i]
      (nth-hypercomponent hyperquiver edge i))
    (hyperquiver-arity hyperquiver)))

; Underlying multirelations of hyperquivers
(defmethod underlying-multirelation NaryHyperquiver
  [^NaryHyperquiver hyperquiver]

  (set
    (map
      (fn [morphism]
        (morphism-hypercomponents hyperquiver morphism))
      (morphisms hyperquiver))))

(defmethod underlying-relation NaryHyperquiver
  [^NaryHyperquiver hyperquiver]

  (set (underlying-multirelation hyperquiver)))

; A relational nary hyperquiver is formed from a set of lists of sets.
(defn relational-nary-hyperquiver
  [rel]

  (let [arity (count (first rel))
        vertices (apply
                   union
                   (map
                     (fn [coll]
                       (apply union coll))
                     rel))]
    (->NaryHyperquiver
      rel
      vertices
      (fn [edge i]
        (nth edge i))
      arity)))

; Multimethods to covert objects into hyperquivers
(defmulti to-nary-hyperquiver type)

(defmethod to-nary-hyperquiver NaryHyperquiver
  [^NaryHyperquiver hyperquiver] hyperquiver)

(defmethod to-nary-hyperquiver Hyperfunction
  [hyperfunction]

  (->NaryHyperquiver
    (source-object hyperfunction)
    (target-object hyperfunction)
    (fn [edge i]
      (hyperfunction edge))
    1))

(defmethod to-nary-hyperquiver Diset
  [diset]

  (->NaryHyperquiver
    (morphisms diset)
    (objects diset)
    (constantly #{})
    0))

(defmethod to-nary-hyperquiver SetFunction
  [func]

  (->NaryHyperquiver
    (inputs func)
    (outputs func)
    (fn [edge i]
      #{(func edge)})
    1))

(defmethod to-nary-hyperquiver NaryQuiver
  [quiver]

  (->NaryHyperquiver
    (morphisms quiver)
    (objects quiver)
    (fn [edge i]
      #{(nth-component edge i)})
    (quiver-arity quiver)))

(defmethod to-nary-hyperquiver :locus.set.logic.core.set/universal
  [coll]

  (relational-nary-hyperquiver coll))

; Hyperquivers can be treated as hyperfunctions, by noting that each morphism is associated to a
; set of objects. This then forms a multivalued function from the set of morphisms of the
; hyperquiver to its set of objects.
(defn hyperquiver-morphism-component-objects-set
  [hyperquiver morphism]

  (apply union (morphism-hypercomponents hyperquiver morphism)))

(defmethod to-hyperfunction NaryHyperquiver
  [^NaryHyperquiver hyperquiver]

  (->Hyperfunction
    (morphisms hyperquiver)
    (objects hyperquiver)
    (fn [morphism]
      (hyperquiver-morphism-component-objects-set hyperquiver morphism))))

; Quivers can also be treated as hyperfunctions, by noting that each morphism is associated to a
; set of objects. In the particular case of binary quivers, these hyperfunctions are always
; rank two as each morphism can be associated with no more than two objects: its source object
; and its target object, but in the general case morphisms in nary quiver can be associated
; to any number of objects.
(defn quiver-morphism-component-objects-set
  [quiver morphism]

  (set (morphism-components quiver morphism)))

(defmethod to-hyperfunction :locus.set.quiver.structure.core.protocols/nary-quiver
  [quiver]

  (->Hyperfunction
    (morphisms quiver)
    (objects quiver)
    (fn [morphism]
      (quiver-morphism-component-objects-set quiver morphism))))

; Images of sets under nary hyperquivers
(defn nary-hyperquiver-set-image
  [hyperquiver coll]

  (letfn [(single-morphism-image [hyperquiver morphism]
            (apply union (morphism-hypercomponents hyperquiver morphism)))]
    (apply
      union
      (map
        (fn [i]
          (single-morphism-image hyperquiver i))
        coll))))

(defn nary-hyperquiver-set-inverse-image
  [hyperquiver objects]

  (set
    (filter
      (fn [morphism]
        (superset? (list (nary-hyperquiver-set-image hyperquiver #{morphism}) objects)))
      (morphisms hyperquiver))))

(defmethod image
  [NaryHyperquiver :locus.set.logic.core.set/universal]
  [hyperquiver coll]

  (nary-hyperquiver-set-image hyperquiver coll))

(defmethod inverse-image
  [NaryHyperquiver :locus.set.logic.core.set/universal]
  [hyperquiver coll]

  (nary-hyperquiver-set-inverse-image hyperquiver coll))

; Ontology of hyperquivers
(defmulti nary-hyperquiver? type)

(defmethod nary-hyperquiver? NaryHyperquiver
  [^NaryHyperquiver hyperquiver] true)

(defmethod nary-hyperquiver? :default
  [obj] false)

(defn unary-hyperquiver?
  [obj]

  (and
    (nary-hyperquiver? obj)
    (= (hyperquiver-arity obj) 1)))

(defn binary-hyperquiver?
  [obj]

  (and
    (nary-hyperquiver? obj)
    (= (hyperquiver-arity obj) 2)))

(defn ternary-hyperquiver?
  [obj]

  (and
    (nary-hyperquiver? obj)
    (= (hyperquiver-arity obj) 3)))

(defn quaternary-hyperquiver?
  [obj]

  (and
    (nary-hyperquiver? obj)
    (= (hyperquiver-arity obj) 4)))
