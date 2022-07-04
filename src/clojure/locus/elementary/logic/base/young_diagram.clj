(ns locus.elementary.logic.base.young-diagram
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.base.sig :refer :all]
            [locus.elementary.function.core.protocols :refer :all]))

; Young diagrams
; Elements in Young's lattice. The lattice Y of young's diagrams is simultaneously
; a thin category and a distributive lattice. Young diagrams are implemented as objects
; of a category with product and coproduct the meet and join operations. This gives
; us a more categorical means of dealing with Young's lattice.
(deftype YoungDiagram [nums]
  Object
  (toString [this]
    (.toString nums)))

(defmethod print-method YoungDiagram [^YoungDiagram v ^java.io.Writer w]
  (.write w (.toString v)))

; Product and coproducts in the thin category of young's diagrams
(defmethod product YoungDiagram
  [& young-diagrams]

  (YoungDiagram.
    (apply young-meet (map #(.nums %) young-diagrams))))

(defmethod coproduct YoungDiagram
  [& young-diagrams]

  (YoungDiagram.
    (apply young-join (map #(.nums %) young-diagrams))))


