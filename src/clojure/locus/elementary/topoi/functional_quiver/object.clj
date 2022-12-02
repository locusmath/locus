(ns locus.elementary.topoi.functional-quiver.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]))

; A functional quiver is a copresheaf in the topos Sets^C where C is the category consisting of
; three objects and six morphisms: the identity morphisms, the source and target morphisms
; of a quiver and another morphism going from the third object of the index category to the
; edge set of the quiver. So in other words, it is a quiver with some function headingt towards
; its edge set. This is not enough to recover the data of a category, since it the function
; adjoined to the quiver does not need to be a binary operation, but it is a partial step
; in that direction.

(deftype FunctionalQuiver [paths morphisms objects op source target]
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this]
    (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this obj] (list (source obj) (target obj))))

; Get the function of the functional quiver that defines it
(defn functional-quiver-domain
  [^FunctionalQuiver quiver]

  (.-paths quiver))

(defn function-of-functional-quiver
  [^FunctionalQuiver quiver]

  (->SetFunction
    (.-paths quiver)
    (.-morphisms quiver)
    (.-op quiver)))

; Get the fiber cardinality of a morphism in a functional quiver like this
(defn morphism-fiber-cardinality
  [quiver morphism]

  (fiber-cardinality (function-of-functional-quiver quiver) morphism))

; Generalized conversion routines
(defmulti to-functional-quiver type)

(defmethod to-functional-quiver FunctionalQuiver
  [quiver] quiver)

; The underlying relations and multirelations of the functional quiver
(defmethod underlying-multirelation FunctionalQuiver
  [quiver]

  (multiset
    (map
      (fn [morphism]
        (transition quiver morphism))
      (morphisms quiver))))

(defmethod underlying-relation FunctionalQuiver
  [quiver] (set (underlying-multirelation quiver)))

(defmethod visualize FunctionalQuiver
  [quiver] (visualize (underlying-multirelation quiver)))

; Products and coproducts in the topos of functional quivers
(defmethod coproduct FunctionalQuiver
  [& quivers]

  (->FunctionalQuiver
    (apply product (map functional-quiver-domain quivers))
    (apply product (map morphisms quivers))
    (apply product (map objects quivers))
    (apply product (map function-of-functional-quiver quivers))
    (apply product (map source-function quivers))
    (apply product (map target-function quivers))))

(defmethod coproduct FunctionalQuiver
  [& quivers]

  (->FunctionalQuiver
    (apply coproduct (map functional-quiver-domain quivers))
    (apply coproduct (map morphisms quivers))
    (apply coproduct (map objects quivers))
    (apply coproduct (map function-of-functional-quiver quivers))
    (apply coproduct (map source-function quivers))
    (apply coproduct (map target-function quivers))))

; Ontology of functional quivers
(defn functional-quiver?
  [quiver]

  (= (type quiver) FunctionalQuiver))