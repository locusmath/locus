(ns locus.graphics.latex.view
  (:require [locus.set.logic.core.set :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.polynomial.core.object :refer :all]
            [locus.variety.affine.impl :refer :all]
            [locus.polynomial.fractional.object :refer :all]
            [locus.order.lattice.term.lattice-term :refer :all])
  (:import (javax.swing JFrame JPanel JLabel)
           (org.scilab.forge.jlatexmath TeXIcon TeXConstants TeXFormula)
           (locus.polynomial.core.object Polynomial)
           (locus.variety.affine.impl AffineVariety)
           (locus.polynomial.fractional.object RationalExpression)
           (locus.order.lattice.term.lattice_term LatticeTerm)))

; This file allows us to treat the various mathematical expressions in Locus
; as though they are in Latex. This allows for an easier visualisation of
; mathematical expressions in their customary notation. On the one hand, we have
; symbolic expressions determined in Clojure and on the other hand we have
; their Latex representations. The to-latex method converts between them.

; Latex expressions
(deftype LatexExpression [expr]
  java.lang.Object
  (toString [this] expr))

(defmethod print-method LatexExpression [^LatexExpression v ^java.io.Writer w]
  (.write w (.toString v)))

; Generalized conversion routines for turning objects into latex
(defmulti to-latex type)

(defmethod to-latex LatexExpression
  [^LatexExpression latex-expression] latex-expression)

; Convert polynomials into latex expressions
(defn latex-monomial-string
  [coefficient terms]

  (let [coefficient-string (cond
                             (and (not (empty? terms)) (= coefficient 1)) ""
                             (and (not (empty? terms)) (= coefficient -1)) "-"
                             :else (str coefficient))]
    (str
      coefficient-string
      (apply
        str
        (map
          (fn [i]
            (let [variable-name (if (number? i)
                                  (str "x_" i)
                                  i)
                  exponentation-string (let [mult (multiplicity terms i)]
                                         (if (= mult 1)
                                           ""
                                           (str "^" (str mult))))]
              (str variable-name exponentation-string)))
          (support terms))))))

(defmethod to-latex Polynomial
  [^Polynomial polynomial]

  (let [monomials (seq (.data polynomial))]
    (LatexExpression.
      (apply
        str
        (let [monomial-strings (map
                                 (fn [[i coefficient]]
                                   (latex-monomial-string coefficient i))
                                 monomials)]
          (map
            (fn [i]
              (if (zero? i)
                (nth monomial-strings i)
                (str
                  (let [[i v] (nth monomials i)]
                    (if (and
                          (number? v)
                          (neg? v))
                      ""
                      " + "))
                  (nth monomial-strings i))))
            (range (count monomial-strings))))))))

(defmethod to-latex RationalExpression
  [^RationalExpression expr]

  (LatexExpression.
    (str
     "\\frac{"
     (.expr (to-latex (numerator-polynomial expr)))
     "}{"
     (.expr (to-latex (denominator-polynomial expr)))
     "}")))

(defmethod to-latex AffineVariety
  [^AffineVariety variety]

  (LatexExpression.
    (str
     "\\["
     (apply
       str
       (map
         (fn [polynomial]
           (str (.expr (to-latex polynomial)) " = 0" "\\\\"))
         (.polynomials variety)))
     "\\]")))

; Convert a given lattice term into latex
(defn lattice-expression-to-latex
  [x]

  (if (not (coll? x))
    (.toString x)
    (let [current-symbol (cond
                           (additive-expression? x) " \\vee "
                           (multiplicative-expression? x) " \\wedge ")]
      (apply
        str
        (interpose
         current-symbol
         (map
           (fn [i]
             (if (coll? i)
               (str "(" (lattice-expression-to-latex i) ")")
               (.toString i)))
           (rest x)))))))

(defmethod to-latex LatticeTerm
  [^LatticeTerm x]

  (LatexExpression.
    (lattice-expression-to-latex
      (.data x))))

; Visualisation of latex expressions using jlatexmath
(defmethod visualize LatexExpression
  [latex-expression]

  (let [^String expr (.expr latex-expression)
        ^JFrame frame (JFrame.)
        ^TeXFormula form (TeXFormula. expr)
        ^TeXIcon icon (.createTeXIcon form TeXConstants/STYLE_DISPLAY 40)]
    (.setTitle frame "Expression viewer")

    (let [^JPanel panel (JPanel.)
          ^JLabel label (JLabel.)]
      (.setIcon label icon)
      (.add panel label)
      (.add frame panel))

    (.setSize frame 400 200)
    (.setVisible frame true)))

