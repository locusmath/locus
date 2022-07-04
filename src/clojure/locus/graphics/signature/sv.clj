(ns locus.graphics.signature.sv
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.logic.base.young-diagram :refer :all])
  (:import [java.awt.image BufferedImage]
           [javax.swing JFrame JLabel ImageIcon]
           (locus.elementary.logic.base.young_diagram YoungDiagram)))

; An additive partition is also equivalently a Young diagram, and there is a customary
; way of visualizing such diagrams. This file exists to create graphical visualisations
; of such Young diagrams that we can use in our programs.

(defn random-signature
  []

  (let [rwidth (int (* (Math/random) 200))
        rheight (int (* (Math/random) 75))]
    (multiset
      (map
        (fn [i]
          (int (* rheight (Math/random))))
        (range rwidth)))))

(defn determine-coordinates
  [coll]

  (let [sorted-seq (sort > (seq coll))]
    (apply
     concat
     (map-indexed
      (fn [x v]
        (map
         (fn [y]
           [x y])
         (range 0 v)))
      sorted-seq))))

(defn signature-image
  [sig block-size]

  (let [coords (determine-coordinates sig)
        sig-width (count sig)
        sig-height (if (empty? sig) 0 (apply max sig))
        padding-size (int (/ block-size 2))
        img-width (+ (* block-size (inc sig-width)))
        img-height (+ (* block-size (inc sig-height)))
        img (BufferedImage.
             img-width
             img-height
             BufferedImage/TYPE_INT_RGB)
        g (.createGraphics img)]
    (.setColor g java.awt.Color/WHITE)
    (.fillRect g 0 0 img-width img-height)
    (.setColor g java.awt.Color/BLACK)
    (doseq [coord coords]
      (let [[x y] coord]
        (.drawRect
         g
         (+ padding-size (* x block-size))
         (- img-height
            (+ padding-size
               (* (inc y) block-size)))
         block-size
         block-size)))
    img))

(defn display-image
  [^BufferedImage img]

  (let [f (JFrame.)]
    (.add (.getContentPane f)
          (JLabel. (ImageIcon. img)))
    (.pack f)
    (.setVisible f true)))

(defn visualize-young-diagram
  [sig]

  (display-image
   (signature-image
    sig
    (let [n (max
             (if (empty? sig) 0 (apply max sig))
             (count sig))]
      (if (<= n 8)
        20
        20)))))

; Visualization routines
(defmethod visualize YoungDiagram
  [^YoungDiagram diagram]

  (visualize-young-diagram (.nums diagram)))





