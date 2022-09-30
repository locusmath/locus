(ns locus.elementary.lattice.term.lattice-term
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lattice.core.morphism :refer :all]
            [locus.elementary.lattice.element.object :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)))

; Lattices are fundamental objects of category theory, as they are thin categories containing all
; binary products and coproducts. However, the products and coproducts of lattice don't always
; distribute with one another. They can instead for arbitrarily large nested trees of
; product and coproduct expressions. In order to better handle this and to make lattice
; terms more accessible to the user we have defined special routines for visualising
; lattice expressions.

; In the topos of Sets, the product of two sets corresponds to the product of two numbers
; by their cardinality. Similarly, the coproduct operation corresponds to the sum of two
; sets and the cardinality of a coproduct of finite sets is the sum of the cardinalities
; of its arguments. Based upon this convention, we refer to the coproduct as +
; and the product as *.

; Translating this into lattice theory, we use + to refer to the join of two objects
; and * to refer to the meet. This way terms in a lattice can be represented symbolically
; using the familiar arithmetic operations + and *. These then are transformed into
; symbolic expressions for representation in the machine so that we can perform
; basic operations on the lattice expressions.

(deftype LatticeTerm [data]
  Object
  (toString [this]
    (.toString data)))

(defmethod print-method LatticeTerm [^LatticeTerm v ^java.io.Writer w]
  (.write w (.toString v)))

; Generalized conversion routines so that arbitrary mathematical and logical objects such as
; boolean formulas can be converted into lattice terms.
(defmulti to-lattice-term type)

(defmethod to-lattice-term LatticeTerm
  [x] x)

; Example lattice terms
(def expoly
  (LatticeTerm.
    '(+ (* a b)
        (* c (+ d e)))))

(def exlt
  (LatticeTerm.
    '(+ a
        (* d e))))

(def exlp
  (LatticeTerm.
    '(* (+ (* a b)
           (* c d)
           e)
        (+ (* f g) h)
        (+ i j k)
        l)))

(def dlp
  (LatticeTerm.
    '(* (+ a b)
        (+ a c)
        (+ b c))))

; We can use individual lattice terms as the building blocks of expressions
(defn singular-lattice-term
  [x]

  (LatticeTerm. x))

; Associativity simplification
(defn simplified-terms
  [combiner expression]

  (if (or (not (coll? expression))
          (empty? expression)
          (not= (first expression) combiner))
    (list expression)
    (mapcat
      (partial simplified-terms combiner)
      (rest expression))))

(defn associativity-simplification
  [combiner expression]

  (if (and (coll? expression)
           (not (empty? expression))
           (= (first expression) combiner))
    (cons
      combiner
      (mapcat
        (partial simplified-terms combiner)
        (rest expression)))
    expression))

; Absorption simplification
(defn superterm?
  [a b]

  (let [first-operands (if (not (coll? a))
                         #{a}
                         (set (rest a)))
        second-operands (if (not (coll? b))
                          #{b}
                          (set (rest b)))]
    (superset? (list first-operands second-operands))))

(defn absorption-simplification
  [coll]

  (cons
    (first coll)
    (distinct
      (let [terms (rest coll)]
        (for [current-term terms
              :when (every?
                      (fn [possible-subterm]
                        (or
                          (= current-term possible-subterm)
                          (not (superterm? possible-subterm current-term))))
                      terms)]
          current-term)))))

; Combined simplification
(defn simplify-lattice-term
  [expr]

  (if (not (coll? expr))
    expr
    (let [current-combiner (first expr)
          associativity-simplified-expr (associativity-simplification
                                          current-combiner
                                          expr)
          simplified-expr (absorption-simplification associativity-simplified-expr)]
      (if (= (count simplified-expr) 2)
        (second simplified-expr)
        simplified-expr))))

(defn simplify-lattice-expression
  [expr]

  (if (not (coll? expr))
    expr
    (let [first-phase (simplify-lattice-term expr)]
      (if (not (coll? first-phase))
        first-phase
        (cons
          (first first-phase)
          (map simplify-lattice-expression (rest first-phase)))))))

; Products and coproducts in free lattices defined as thin categories
(defmethod product LatticeTerm
  [& terms]

  (LatticeTerm.
    (simplify-lattice-expression
      (cons
        '*
        (map #(.data %) terms)))))

(defmethod coproduct LatticeTerm
  [& terms]

  (LatticeTerm.
    (simplify-lattice-expression
      (cons
        '+
        (map #(.data %) terms)))))

; Construction of free lattices
(defn free-lattice-expression?
  [coll expr]

  (if (not (coll? expr))
    (contains? coll expr)
    (every?
      (fn [i]
        (free-lattice-expression? coll i))
      (rest expr))))

(defn free-lattice-element?
  [coll expr]

  (and
    (= (type expr) LatticeTerm)
    (= (.data expr)
       (simplify-lattice-expression (.data expr)))
    (free-lattice-expression? coll (.data expr))))

(defn free-lattice
  [coll]

  (Lattice.
    (partial free-lattice-element? coll)
    coproduct
    product))

; Apply a lattice expression
; Specifically this requires that the data is a symbolic expression
; such as a coll or a constant term
(defn apply-lattice-expression
  [join meet data env]

  (if (not (coll? data))
    (get env data)
    (let [sym (first data)]
      (apply
        (cond
          (= sym '+) join
          (= sym '*) meet)
        (map
          (fn [i]
            (apply-lattice-expression join meet i env))
          (rest data))))))

; Meet and join normal forms
(defn multiplicative-expression?
  [expr]

  (and
    (coll? expr)
    (not (empty? expr))
    (= (first expr) '*)))

(defn additive-expression?
  [expr]

  (and
    (coll? expr)
    (not (empty? expr))
    (= (first expr) '+)))

(defn simple-multiplicative-expression?
  [expr]

  (and
    (multiplicative-expression? expr)
    (every?
      (fn [i]
        (not (coll? i)))
      (rest expr))))

(defn simple-additive-expression?
  [expr]

  (and
    (additive-expression? expr)
    (every?
      (fn [i]
        (not (coll? i)))
      (rest expr))))

(defn join-normal-expression?
  [expr]

  (letfn [(term? [x]
            (or
              (not (coll? x))
              (simple-multiplicative-expression? x)))]
    (or
      (term? expr)
      (and
        (additive-expression? expr)
        (every? term? (rest expr))))))

(defn meet-normal-expression?
  [expr]

  (letfn [(term? [x]
            (or
              (not (coll? x))
              (simple-additive-expression? x)))]
    (or
      (term? expr)
      (and
        (multiplicative-expression? expr)
        (every? term? (rest expr))))))

; Ontology of lattice terms
(defn lattice-term?
  [term]

  (= (type term) LatticeTerm))

(defn join-normal-lattice-term?
  [term]

  (and
    (lattice-term? term)
    (join-normal-expression? (.data ^LatticeTerm term))))

(defn meet-normal-lattice-term?
  [term]

  (and
    (lattice-term? term)
    (meet-normal-expression? (.data ^LatticeTerm term))))


