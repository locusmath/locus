(ns locus.graph.directed.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]))

; Digraph
; The category of digraphs can be interpreted topos theoretically in terms of the fundamental
; topos of quivers. In this context, the category of digraphs is simply the subcategory
; consisting of thin quivers. We provide the to-quiver method in order to interpret
; the category of directed graphs more topos theoretically.

(deftype Digraph [vertices edges]
  ConcreteObject
  (underlying-set [this] vertices))

(derive Digraph :locus.elementary.function.core.protocols/structured-set)

(defmethod to-quiver Digraph
  [^Digraph digraph]

  (thin-quiver (underlying-set digraph) (underlying-relation digraph)))

(defmethod underlying-relation Digraph
  [^Digraph digraph]

  (.edges digraph))

(defmethod visualize Digraph
  [^Digraph digraph] (visualize (underlying-relation digraph)))

(defn digraph
  [rel]

  (Digraph. (vertices rel) rel))



