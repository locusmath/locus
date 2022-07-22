(ns locus.graphics.core.alt
  (:import (javafx.scene Group Scene)
           (javafx.scene.layout Pane)
           (javafx.application Platform)
           (locus.ui.quiver.layout LayoutMaker)
           (locus.ui.quiver.hom HomMaker)
           (locus.ui.quiver.graph GraphActionListener GraphMaker)
           (locus.ui.util SceneViewer)
           (locus.ui.quiver BaseApplication)))

(defn nested-array
  [coll]

  (into-array (map into-array coll)))

(defn integer-array
  [coll]

  (into-array
    (map
      (fn [i]
        (into-array
          (map #(Integer/valueOf (int %)) i)))
      coll)))

; Test graph layout
(def nodes
  (LayoutMaker/layoutGraph
    (nested-array
      [["a"]
       ["b"]])))

(def edges
  (HomMaker/getHomClassesByPartition
    (nested-array
      [["f" "a" "b"]
       ["f*" "b" "a"]])
    (integer-array [[0 1]])))

(defn main
  []

  (Platform/startup
    (reify Runnable
      (run [this]
        (let [scene (GraphMaker/makeGraphScene
                      nodes
                      edges
                      (reify GraphActionListener
                        (vertexAction [this e]
                          (prn e))
                        (edgeAction [this e]
                          (prn e)))
                      600
                      600)]
          (SceneViewer. "Graph viewer" scene))))))
