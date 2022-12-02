(ns locus.order.boolean.formula.core
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.quiver.relation.binary.sr :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.order.boolean.algebra.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.term.lattice-term :refer :all])
  (:import (locus.order.boolean.algebra.object BooleanAlgebra)))

; Construct a boolean formula on a set from a set of signed sets
; A given literal in a signed set is associated to negative one if it is
; negated and it is associated to one otherwise. This allows us to provide
; a numeric representation of boolean formulas. In the case of boolean formulas
; over a positive integer range, the sign is provided numerically.
(deftype DisjunctiveNormalFormula [literals clauses])
(deftype ConjunctiveNormalFormula [literals clauses])

(derive DisjunctiveNormalFormula ::boolean-formula)
(derive ConjunctiveNormalFormula ::boolean-formula)

(defn boolean-formula?
  [formula] (isa? (type formula) ::boolean-formula))

; The subset to signed set utility function is helpful for creating
; certain boolean formulas that are associated to set systems
(defn subset-to-signed-set
  [elems parent]

  (into
    {}
    (map
      (fn [i]
        [i (if (elems i)
             1
             -1)])
      parent)))

; implication clauses only require two literals
(defn implication-clause
  [x y]

  (if (= x y)
    {}
    {x -1
     y 1}))

; This is a simple utility method for creating horn clauses described
; using our system of signed sets
(defn definite-clause
  [conditions result]

  (into
    {}
    (conj
      (map
        (fn [i]
          [i -1])
        conditions)
      [result 1])))

; Goal clauses contain only negated literals
(defn goal-clause
  [conditions]

  (into
    {}
    (conj
      (map
        (fn [i]
          [i -1])
        conditions))))

; This combines two clauses either by meeting two conjunctive clauses
; or joining two disjunctive clauses. In both cases, if we have negated
; pairs of literals in the combination then this reduces to nothing.
(defn combine-clauses
  [a b]

  (let [a-keys (keys a)
        b-keys (keys b)
        common-keys (intersection (set a-keys) (set b-keys))
        lacks-negated-pairs? (every?
                               (fn [i]
                                 (= (get a i) (get b i)))
                               common-keys)]
    (if lacks-negated-pairs?
      (merge a b)
      {})))

; Negate the signs of a clause expressed as a sign set
(defn negate-clause
  [x]

  (into
    {}
    (map
     (fn [key]
       [x (- (get key x))])
     (keys x))))

; Check if a given boolean clause implies another
(defn boolean-subclause?
  [child-clause parent-clause]

  (let [child-keys (set (keys child-clause))
        parent-keys (set (keys parent-clause))]
    (and
      (superset? (list child-keys parent-keys))
      (every?
        (fn [i]
          (= (get child-clause i) (get parent-clause i)))
        child-keys))))

(defn proper-boolean-subclause?
  [a b]

  (and
    (not= a b)
    (boolean-subclause? a b)))

; The negation of boolean formulas can be computed by DeMorgan's laws
; In this case we simply see that
(defmulti negate-boolean-formula type)

(defmethod negate-boolean-formula ConjunctiveNormalFormula
  [^ConjunctiveNormalFormula formula]

  (DisjunctiveNormalFormula.
    (.literals formula)
    (map negate-clause (.clauses formula))))

(defmethod negate-boolean-formula DisjunctiveNormalFormula
  [^DisjunctiveNormalFormula formula]

  (ConjunctiveNormalFormula.
    (.literals formula)
    (map negate-clause (.clauses formula))))

; Simplify boolean formulas by removing all redundant terms
(defn remove-redundant-clauses
  [clause-system]

  (filter
    (fn [clause]
      (every?
        (fn [possible-child-clause]
          (not (proper-boolean-subclause? possible-child-clause clause)))
        clause-system))
    clause-system))

(defmulti simplify-boolean-formula type)

(defmethod simplify-boolean-formula ConjunctiveNormalFormula
  [^ConjunctiveNormalFormula formula]

  (ConjunctiveNormalFormula.
    (.literals formula)
    (remove-redundant-clauses (.clauses formula))))

(defmethod simplify-boolean-formula DisjunctiveNormalFormula
  [^DisjunctiveNormalFormula formula]

  (DisjunctiveNormalFormula.
    (.literals formula)
    (remove-redundant-clauses (.clauses formula))))

; This demonstrates the relationship between set systems and boolean formulas
(defn family->formula
  ([sets] (family->formula (dimembers sets) sets))
  ([coll sets]
   (DisjunctiveNormalFormula.
     coll
     (map
       (fn [i]
         (subset-to-signed-set i coll))
       sets))))

; Preorders are boolean formulas by defining every order pair in the
; preorder as a logical implication of a boolean formula. This then
; produces a set system of solutions to the preorder, corresponding to
; its lattice of ideals.
(defn preorder->formula
  [rel]

  (let [coll (vertices rel)]
    (ConjunctiveNormalFormula.
      coll
      (for [[a b] rel
            :when (not= a b)]
        {a -1, b 1}))))

; Check for boolean satisfiability on the level of clauses
(defn satisfies-literal-condition?
  [literal multiplicity term]

  (if (= multiplicity 1)
    (contains? term literal)
    (not (contains? term literal))))

(defn satisfies-conjunctive-clause?
  [conjunctive-clause term]

  (every?
    (fn [[i v]]
      (satisfies-literal-condition? i v term))
    conjunctive-clause))

(defn satisfies-disjunctive-clause?
  [disjunctive-clause term]

  (not
    (every?
      (fn [[i v]]
        (not
          (satisfies-literal-condition? i v term)))
      disjunctive-clause)))

; Boolean satisfiability support
(defmulti boolean-formula-solution? (fn [i v] (type i)))

(defmethod boolean-formula-solution? ConjunctiveNormalFormula
  [formula term]

  (every?
    (fn [i]
      (satisfies-disjunctive-clause? i term))
    (.clauses formula)))

(defmethod boolean-formula-solution? DisjunctiveNormalFormula
  [formula term]

  (not
    (every?
     (fn [i]
       (not
         (satisfies-conjunctive-clause? i term)))
     (.clauses formula))))

; Get all solutions of a given boolean formula
(defn boolean-formula-solutions
  [formula]

  (set
    (filter
      (fn [i]
        (boolean-formula-solution? formula i))
      (power-set (.literals formula)))))

; A boolean variable in a formula
(deftype BooleanFormulaVariable [variable negated]
  java.lang.Object
  (toString [this]
    (if negated
      (str "¬" variable)
      (str variable))))

(defmethod print-method BooleanFormulaVariable
  [^BooleanFormulaVariable v, ^java.io.Writer w]

  (.write w (.toString v)))

; Get a lattice expression from a dnf boolean formula
(defmethod to-lattice-term DisjunctiveNormalFormula
  [^DisjunctiveNormalFormula formula]

  (->LatticeTerm
    (simplify-lattice-expression
     (cons
       '+
       (map
         (fn [conjunctive-clause]
           (cons
             '*
             (map
               (fn [[i v]]
                 (BooleanFormulaVariable. i (neg? v)))
               conjunctive-clause)))
         (.clauses formula))))))

(defmethod to-lattice-term ConjunctiveNormalFormula
   [^ConjunctiveNormalFormula formula]

  (->LatticeTerm
    (simplify-lattice-expression
     (cons
       '*
       (map
         (fn [disjunctive-clause]
           (cons
             '+
             (map
               (fn [[i v]]
                 (BooleanFormulaVariable. i (neg? v)))
               disjunctive-clause)))
         (.clauses formula))))))



