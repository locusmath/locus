;(ns locus.graphics.chart.infographics
;  (:require [locus.base.logic.core.set :refer :all]
;            [locus.base.logic.numeric.natural :refer :all])
;  (:import (org.jfree.data.general DefaultPieDataset)
;           (org.jfree.chart ChartFactory ChartPanel)
;           (org.jfree.chart.ui ApplicationFrame)
;           (javax.swing JFrame)))

; The JFreeChart library provides a number of built in charts that we can use in Locus.
; In doing so we will be able to create better visualisations. The key to this process
; is creating a Clojure based interface to the JFreeChart library.

;(defn create-chart
;  [name data]
;
;  (let [dataset (DefaultPieDataset.)]
;    (doseq [[i v] data]
;      (.setValue dataset i v))
;    (ChartFactory/createPieChart name dataset true true false)))
;
;(defn visualize-factors
;  [n]
;
;  (let [frame (JFrame. "Prime Distribution")
;        data (multiplicities-map (factors n))]
;    (.setSize frame 500 500)
;    (.setContentPane frame (new ChartPanel (create-chart (.toString n) data)))
;    (.setVisible frame true)))
