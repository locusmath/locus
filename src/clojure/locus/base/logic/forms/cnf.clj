(ns locus.base.logic.forms.cnf
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]))

; disjunctive normal form of a set
(deftype CNFS [clause]
  clojure.lang.IFn
  (invoke [this obj]
    (every?
      (fn [disjunctive-clause]
        (not
          (every?
            (fn [term]
              (not
                (term obj)))
            disjunctive-clause)))
      clause))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive CNFS :locus.base.logic.core.set/universal)

(defmethod intersection* #{CNFS}
  [^CNFS a, ^CNFS b]

  (CNFS. (union (.clause a) (.clause b))))

(defmethod union* #{CNFS}
  [^CNFS a, ^CNFS b]

  (CNFS.
    (set
      (for [a-term (.clause a)
            b-term (.clause b)]
        (union a-term b-term)))))




