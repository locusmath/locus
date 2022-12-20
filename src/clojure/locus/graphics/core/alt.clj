(ns locus.graphics.core.alt
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.copresheaf.bijection.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.algebra.category.core.morphism :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.set.action.global.object :refer :all])
  (:import (javafx.scene Group Scene)
           (javafx.scene.layout Pane)
           (javafx.application Platform)
           (locus.ui.quiver.layout LayoutMaker LabeledEntity)
           (locus.ui.quiver.hom HomMaker EdgeData)
           (locus.ui.quiver.graph GraphActionListener GraphMaker)
           (locus.ui.util SceneViewer)
           (locus.ui.quiver BaseApplication)
           (javax.swing JFrame)
           (java.util ArrayList Collection)))

; utility helper functions
(defn nested-array
  [coll]

  (into-array (map into-array coll)))

(defn nested-array-list
  [coll]

  (ArrayList.
    ^Collection
    (map
      (fn [i]
        (ArrayList. ^Collection (map int i)))
      coll)))

; Generalized display mechanism for the newer quiver viewer
(defn get-nodes
  [q]

  (LayoutMaker/layoutGraph
    (nested-array
      (map
        (fn [i]
          (map
            #(LabeledEntity/getInstance %)
            i))
        (lower-first-ranking (cl reflexive? (underlying-relation q)))))))

(defn get-edges
  [q]

  (HomMaker/getHomClasses
    (into-array
      (map
        (fn [morphism]
          (EdgeData.
            morphism
            (.toString morphism)
            (source-element q morphism)
            (target-element q morphism)))
        (morphisms q)))))

(defn display-quiver
  [quiver listener]

  (let [scene (GraphMaker/makeGraphScene
                (get-nodes quiver)
                (get-edges quiver)
                listener
                600
                600)]
    (SceneViewer. "Copresheaf viewer" scene)))

(defn display-copresheaf
  [copresheaf]

  (display-quiver
    (morphically-generated-subquiver (source-object copresheaf))
    (reify GraphActionListener
      (vertexAction [this e]
        (visualize (identity-function (object-apply copresheaf e))))
      (edgeAction [this e]
        (visualize (morphism-apply copresheaf e))))))

; This is the main function
(defn main
  []

  (Platform/startup
    (reify Runnable
      (run [this]
        (display-copresheaf
          (to-copresheaf (to-quiver {:x 1 :y 2})))))))
