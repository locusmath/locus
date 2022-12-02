(ns locus.quiver.ternary.algebraic.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.quiver.relation.binary.br :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.quiver.ternary.core.object :refer :all]))

; Algebraic ternary quivers: an algebraic ternary quiver is a thin ternary quiver in which all
; morphisms can be identified by the results of their first and second component functions.
; Then as it happens, the third component function is simply an algebraic binary operation on
; the morphisms of the ternary quiver, whose inputs are determined by their presentation as
; ordered pairs of their first and second parts. As it happens, the full subcategory of algebraic
; ternary quivers of the topos Sets^{T_{2,3}} is isomorphic to the category of partial magmas
; and partial magma homomorphisms.
(deftype ATQuiver [edges vertices op]
  StructuredDiset
  (first-set [this] edges)
  (second-set [this] vertices)

  ConcreteObject
  (underlying-set [this] (->CartesianCoproduct [(first-set [this]) (second-set [this])]))

  StructuredTernaryQuiver
  (first-component-fn [this] first)
  (second-component-fn [this] second)
  (third-component-fn [this] op))

(derive ATQuiver :locus.quiver.base.core.protocols/at-quiver)

; Easy access to domain binary relations for algebraic ternary quivers
(defmethod domain-binary-relation ATQuiver
  [^ATQuiver quiver]

  (.-edges quiver))

; Create an algebraic ternary quiver if that is at all possible
(defn at-quiver
  [edges vertices op]

  (->ATQuiver
    edges
    vertices
    op))

(defn relational-at-quiver
  [rel]

  (loop [coll (seq rel)
         edges #{}
         vertices #{}
         op {}]
    (if (empty? coll)
      (at-quiver edges vertices op)
      (let [elem (first coll)
            [a b c] elem
            source (list a b)]
        (recur
          (conj edges source)
          (union vertices (set elem))
          (conj op [source c]))))))

(defn magma-quiver
  [vertices op]

  (->ATQuiver
    (->CompleteRelation vertices)
    vertices
    op))

; Algebraic ternary quivers also have their own duals
(defmethod dual ATQuiver
  [^ATQuiver quiver]

  (let [op (third-component-fn quiver)]
    (->ATQuiver
     (set (map reverse (morphisms quiver)))
     (objects quiver)
     (fn [morphism]
       (op (reverse morphism))))))

; Get a multiplication map for an at-quiver
(defmethod display-table ATQuiver
  [^ATQuiver quiver] (display-table (third-component-function quiver)))
