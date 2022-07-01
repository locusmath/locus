(ns locus.elementary.boolean.interfaces.sat4j
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.boolean.formula.core :refer :all])
  (:import [org.sat4j.minisat SolverFactory]
           [org.sat4j.core VecInt]
           [org.sat4j.specs IProblem]
           (locus.elementary.boolean.formula.core ConjunctiveNormalFormula)))

; This is to interface between locus boolean formulas and the boolean
; formulas provided by sat4j for solving purposes.
(defn boolean-formula-numerics
  [formula]

  (let [literals (.literals formula)
        clauses (.clauses formula)
        numeric-map (into
                      {}
                      (let [ordered-literals (seq literals)]
                        (map
                          (fn [i]
                            [(nth ordered-literals i) (inc i)])
                          (range (count ordered-literals)))))]
    (map
      (fn [clause]
        (set
          (map
            (fn [[i v]]
              (* (get numeric-map i) v))
            clause)))
      clauses)))

; Create a SAT4j solver
(defn make-sat-solver
  [number-of-variables clauses]

  (let [solver (SolverFactory/newDefault)]
    (.newVar solver number-of-variables)
    (doseq [clause clauses]
      (.addClause solver (new VecInt (int-array clause))))
    solver))

; Convert locus boolean formulas into sat4j ones
(defmulti to-sat-solver type)

(defmethod to-sat-solver ConjunctiveNormalFormula
  [^ConjunctiveNormalFormula formula]

  (make-sat-solver
    (count (.literals formula))
    (boolean-formula-numerics formula)))

; In order to improve performance it is often valuable for
; us to make use of existing Java libraries like SAT4j by
; interfacing with them. The final-model method in this file
; handles the solution of boolean formulas using SAT4j.
(defn find-model
  [^IProblem sat-problem]

  (.findModel sat-problem))







