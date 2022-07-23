(ns locus.graphics.core.alt
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (javafx.scene Group Scene)
           (javafx.scene.layout Pane)
           (javafx.application Platform)
           (locus.ui.quiver.layout LayoutMaker)
           (locus.ui.quiver.hom HomMaker)
           (locus.ui.quiver.graph GraphActionListener GraphMaker)
           (locus.ui.util SceneViewer)
           (locus.ui.quiver BaseApplication)
           (javax.swing JFrame)
           (java.util ArrayList Collection)))

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
          (map #(.toString %) i))
        (lower-first-ranking (cl reflexive? (underlying-relation q)))))))

(defn get-edges
  [q]

  (HomMaker/getHomClasses
    (nested-array
      (map
        (fn [morphism]
          [(.toString morphism)
           (.toString (source-element q morphism))
           (.toString (target-element q morphism))])
        (morphisms q)))))

(defn display-quiver
  [quiver listener]

  (let [scene (GraphMaker/makeGraphScene
                (get-nodes quiver)
                (get-edges quiver)
                listener
                600
                600)]
    (SceneViewer. "Quiver veiwer" scene)))

; This is the main function
(defn main
  []

  (Platform/startup
    (reify Runnable
      (run [this]
        (display-quiver
          (morphically-generated-subquiver triangle-category)
          (reify GraphActionListener
            (vertexAction [this e])
            (edgeAction [this e])))))))