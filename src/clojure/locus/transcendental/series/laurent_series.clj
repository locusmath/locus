(ns locus.transcendental.series.laurent-series
  (:refer-clojure :exclude [+ - * /])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.ab.vector.rset :refer :all]))

; We need to construct the formal laurent series ring R((X)) of a ring, because
; this produces the field of fractions of the power series ring of a field. A formal laurent
; series has laurent polynomial components, which are produced by the localisation of
; the polynomial ring by the multiplicative set of monomials.
(deftype FormalLaurentSeries [ring start terms]
  RingedSet
  (ring-of-coefficients [this] ring)
  (terms [this]
    (fn [i]
      (and
        (integer? i)
        (<= i start))))
  (coefficient [this n]
    (terms n)))

; Generic arithmetic operations in the ring R((X)) of formal laurent series
(defmethod negate FormalLaurentSeries
  [^FormalLaurentSeries series]
  
  (FormalLaurentSeries.
    (.ring series)
    (.start series)
    (fn [i]
      (- (coefficient series i)))))

(defmethod add FormalLaurentSeries
  [^FormalLaurentSeries series1, ^FormalLaurentSeries series2]

  (FormalLaurentSeries.
    (.ring series1)
    (.start series1)
    (fn [i]
      (+ (coefficient series1 i) (coefficient series2 i)))))

; Get the indices in laurent series multiplication
(defn get-laurent-indices
  [n m i]

  (let [current-m (- i n)]
    (if (< current-m m)
      '()
      (cons (list n current-m) (get-laurent-indices (inc n) m i)))))

(defmethod multiply FormalLaurentSeries
  [^FormalLaurentSeries series1, ^FormalLaurentSeries series2]

  (let [base-ring (.ring series1)
        n (.start series1)
        m (.start series2)]
    (FormalLaurentSeries.
     base-ring
     (+ n m)
     (fn [i]
       (apply
         +
         (map
           (fn [[x y]]
             (* (coefficient series1 x)
                (coefficient series2 y)))
           (get-laurent-indices n m i)))))))
