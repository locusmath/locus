(ns locus.calculus.finite.dq
  (:require [locus.elementary.logic.base.core :refer :all]))

; Compute the difference quotient without using limits
; The derivative of a function is then simply the limit of this difference quotient
; as the h value goes to zero. We can use this as a starting point into the
; differential calculus of mathematical functions.

(defn difference-quotient
  [f a h]

  (/ (- (f (+ a h)) (f a)) h))
