(ns locus.partial.quiver.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.nary.core.object :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.partial.mapping.function :refer :all]))

; A partial nary quiver is a structure copresheaf F: T_{2,n} -> Sets_{Part} which targets
; the concrete category of sets and partial functions. It can be considered to be a special
; type of structure copresheaf in our ontology. Important is that partial nary quivers
; have well-defined images and inverse images for sets, which are provided by combining
; the set images and inverse images of the individual partial functions of the quiver.
(deftype PartialNaryQuiver [edges vertices nth-component arity]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices))

(derive PartialNaryQuiver :locus.set.copresheaf.structure.core.protocols/structure-copresheaf)

; Get the arity of a partial nary quiver
(defmulti partial-quiver-arity type)

(defmethod partial-quiver-arity PartialNaryQuiver
  [quiver]

  (.-arity quiver))

; Get the nth component partial function of a partial nary quiver
(defn nth-component-partial-function
  [quiver i]

  (let [func (.-nth_component quiver)]
    (func i)))

; Include partial nary quivers into the copresheaves framework
(defmethod get-object PartialNaryQuiver
  [quiver i]

  (case i
    0 (morphisms quiver)
    1 (objects quiver)))

(defmethod get-morphism PartialNaryQuiver
  [quiver i]

  (cond
    (= i 0) (partial-identity-function (morphisms quiver))
    (= i 1) (partial-identity-function (objects quiver))
    :else (nth-component-partial-function quiver (- i 2))))

(defmethod get-set PartialNaryQuiver
  [quiver i]

  (multiselection (get-object quiver i) #{0 1}))

(defmethod get-function PartialNaryQuiver
  [quiver i]

  (to-function (get-morphism quiver i)))

; A conversion routine for partial nary quivers
(defmethod to-nary-quiver PartialNaryQuiver
  [quiver]

  (->NaryQuiver
    (multiselection (morphisms quiver) #{0 1})
    (multiselection (objects quiver) #{0 1})
    (fn [edge i]
      (partial-function-set-image (nth-component-partial-function quiver i) #{edge}))
    (partial-quiver-arity quiver)))

; Conversion routines for partial nary quivers
(defmulti to-partial-nary-quiver type)

(defmethod to-partial-nary-quiver PartialNaryQuiver
  [quiver] quiver)

(defmethod to-partial-nary-quiver :locus.set.quiver.structure.core.protocols/diset
  [diset]

  (->PartialNaryQuiver
    (morphisms diset)
    (objects diset)
    []
    0))

(defmethod to-partial-nary-quiver :locus.partial.mapping.function/partial-function
  [func]

  (->PartialNaryQuiver
    (source-object func)
    (target-object func)
    (constantly func)
    1))

(defmethod to-partial-nary-quiver :locus.set.logic.structure.protocols/set-function
  [func]

  (->PartialNaryQuiver
    (source-object func)
    (target-object func)
    (constantly (to-partial-function func))
    1))

; Images and inverse images of sets under partial nary quivers
(defn partial-nary-quiver-set-image
  [quiver coll]

  (apply
    union
    (map
      (fn [i]
        (let [func (nth-component-partial-function quiver i)]
          (partial-function-set-image func i)))
      (range (partial-quiver-arity quiver)))))

(defn partial-nary-quiver-set-inverse-image
  [quiver coll]

  (set
    (filter
      (fn [morphism]
        (superset? (list (partial-nary-quiver-set-image quiver #{morphism}) coll)))
      (morphisms quiver))))

(defmethod image
  [PartialNaryQuiver :locus.set.logic.core.set/universal]
  [quiver coll]

  (partial-nary-quiver-set-image quiver coll))

(defmethod inverse-image
  [PartialNaryQuiver :locus.set.logic.core.set/universal]
  [quiver coll]

  (partial-nary-quiver-set-inverse-image quiver coll))

; Ontology of partial nary quivers
(defmulti partial-nary-quiver? type)

(defmethod partial-nary-quiver? PartialNaryQuiver
  [quiver] true)

(defmethod partial-nary-quiver? :default
  [quiver] false)

(defn partial-unary-quiver?
  [quiver]

  (and
    (partial-nary-quiver? quiver)
    (= (partial-quiver-arity quiver) 1)))

(defn partial-binary-quiver?
  [quiver]

  (and
    (partial-nary-quiver? quiver)
    (= (partial-quiver-arity quiver) 2)))

(defn partial-ternary-quiver?
  [quiver]

  (and
    (partial-nary-quiver? quiver)
    (= (partial-quiver-arity quiver) 3)))

(defn partial-quaternary-quiver?
  [quiver]

  (and
    (partial-nary-quiver? quiver)
    (= (partial-quiver-arity quiver) 4)))