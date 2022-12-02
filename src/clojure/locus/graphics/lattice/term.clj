(ns locus.graphics.lattice.term
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.term.lattice-term :refer :all])
  (:import (locus.order.lattice.term.lattice_term LatticeTerm)))

(require '[dorothy.core :as dot])
(require '[dorothy.jvm :refer (render save! show!)])

; This file exists to allow us to take a given lattice term and display it as a
; highlighted tree. The meet operation is displayed as red while the join operation
; is displayed as green in the resulting tree graph. This highlights the fact
; that for any given lattice L the meet is always less then or equal to the join.

(defn get-coordinates
  "Get the coordinates of the leaf nodes of an S-expression."
  [coll]

  (if (not (seq? coll))
    '(())
    (apply
      concat
      (map
        (fn [i]
          (map
            (fn [c]
              (cons i c))
            (get-coordinates (nth coll i))))
        (range (count coll))))))

(defn get-coordinate-value
  "Get the value of an S-expression at the given coordinate."
  [coll coordinate]

  (if (empty? coordinate)
    coll
    (get-coordinate-value
      (nth coll (first coordinate))
      (rest coordinate))))

(defn create-digraph
  "Create a digraph from the arithmetical form of a lattice polynomial."
  [coll]

  (letfn [(create-vertex [coll coordinate]
            (let [v (get-coordinate-value coll coordinate)]
              (cond
                (= v '*) [(.toString coordinate) {:label     ""
                                                  :fillcolor "crimson"
                                                  :style     "filled"}]
                (= v '+) [(.toString coordinate) {:label     ""
                                                  :fillcolor "green"
                                                  :style     "filled"}]
                :else [(.toString coordinate) {:label (.toString v)}])))
          (create-vertices [coll coordinates]
            (concat
              (map
                (partial create-vertex coll)
                coordinates)))
          (find-next-leaf [coll coordinate]
            (if (seq? (get-coordinate-value coll coordinate))
              (find-next-leaf coll (concat coordinate (list 0)))
              coordinate))
          (successor-edges [coordinate]
            (let [fixed-coordinate (if (<= (count coordinate) 1)
                                     '()
                                     (butlast coordinate))
                  parent-sequence (get-coordinate-value coll fixed-coordinate)]
              (map
                (fn [i]
                  [(.toString (seq (concat fixed-coordinate (list 0))))
                   (.toString (seq (find-next-leaf coll (concat fixed-coordinate (list i)))))])
                (range 1 (count parent-sequence)))))
          (create-edges [coll coordinates]
            (apply
              concat
              (for [i coordinates
                    :when (= (last i) 0)]
                (successor-edges i))))]
    (let [coordinates (get-coordinates coll)]
      (vec
        (concat
          (create-vertices coll coordinates)
          (create-edges coll coordinates))))))

; Special showing methods
(defn visualize-lattice-expression
  [coll]

  (-> (create-digraph coll)
      dot/dot
      (show! {:frame-height 10000 :frame-width 10000})))

; Make it so that lattice terms can be visualized
(defmethod visualize LatticeTerm
  [^LatticeTerm term]

  (visualize-lattice-expression (.data term)))