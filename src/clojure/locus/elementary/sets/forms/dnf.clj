(ns locus.elementary.sets.forms.dnf
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]))

; disjunctive normal form of a set
(deftype DNFS [clause]
  clojure.lang.IFn
  (invoke [this obj]
    (not
      (every?
        (fn [conjuctive-set]
          (not
            (every?
              (fn [predicate]
                (predicate obj))
              conjuctive-set)))
        clause)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(defmethod union* #{DNFS}
  [^DNFS a, ^DNFS b]

  (DNFS. (union (.clause a) (.clause b))))

(defmethod intersection* #{DNFS}
  [^DNFS a, ^DNFS b]

  (DNFS.
    (set
     (for [a-term (seq (.clause a))
           b-term (seq (.clause b))]
       (union a-term b-term)))))


