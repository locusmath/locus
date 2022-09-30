(ns locus.stat.commons.statistics
  (:require [locus.base.logic.core.set :refer :all])
  (:import [org.apache.commons.math3.stat Frequency StatUtils]
           (org.apache.commons.math3.stat.correlation Covariance)))

; Convert from a Clojure multiset into an apache commons math frequency
(defn multiset->frequency
  [coll]

  (let [^Frequency rval (Frequency.)]
    (doseq [i coll]
      (.addValue rval i))
    rval))

; Statistic utility wrappers that automatically create java arrays
(defn mean
  [nums]

  (StatUtils/mean (double-array nums)))

(defn geometric-mean
  [nums]

  (StatUtils/geometricMean (double-array nums)))

(defn mode
  [nums]

  (StatUtils/mode (double-array nums)))

(defn variance
  [nums]

  (StatUtils/variance (double-array nums)))

(defn normalize
  [nums]

  (StatUtils/normalize (double-array nums)))

; Covariance matrices
(defn covariance-matrix
  [matrix]

  (.computeCovarianceMatrix (Covariance.) matrix))





