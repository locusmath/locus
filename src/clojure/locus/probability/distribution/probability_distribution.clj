(ns locus.probability.distribution.probability-distribution
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.numeric.natural :refer :all])
  (:import [org.apache.commons.math3.distribution EnumeratedIntegerDistribution GeometricDistribution HypergeometricDistribution ZipfDistribution PascalDistribution UniformIntegerDistribution NormalDistribution UniformRealDistribution LogNormalDistribution ChiSquaredDistribution BinomialDistribution]))

; Create probability distributions using apache commons math
(defn binomial-distribution
  [trials p]

  (BinomialDistribution. trials p))

(defn geometric-distribution
  [p]

  (GeometricDistribution. p))

(defn hypergeometric-distribution
  [p n s]

  (HypergeometricDistribution. p n s))

(defn pascal-distribution
  [r p]

  (PascalDistribution. r p))

(defn uniform-distribution
  [lower upper]

  (UniformIntegerDistribution. lower upper))

(defn zipf-distribution
  [n e]

  (ZipfDistribution. n e))

(defn enumerated-integer-distribution
  [nums]

  (EnumeratedIntegerDistribution. (int-array nums)))

; The probability distribution corresponding to the prime factors of an integer
(defn factors-distribution
  [n]

  (enumerated-integer-distribution (factors n)))

; Continuous probability distributions
(defn normal-distribution
  [mean sd]

  (NormalDistribution. mean sd))

(defn uniform-real-distribution
  [lower upper]

  (UniformRealDistribution. lower upper))

(defn log-normal-distribution
  ([] (LogNormalDistribution.))
  ([double shape] (LogNormalDistribution. double shape))
  ([double shape accuracy] (LogNormalDistribution. double shape accuracy)))

(defn chi-squared-distribution
  ([d] (ChiSquaredDistribution. d))
  ([d i] (ChiSquaredDistribution. d i)))