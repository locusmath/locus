(ns locus.order.lattice.term.identities
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.order.lattice.term.lattice-term :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (locus.order.lattice.term.lattice_term LatticeTerm)))

; Let L be a distributive lattice, then the lattice terms in L satisfy
; the meet and join distributive laws. These can be used to convert lattice
; expressions into either join or meet normal forms. In order to implement these
; normalisation routines over arbitrary lattices we provide additional functions
; that handle lattice terms and expressions.

; Meet distribution of lattice polynomial expressions
(defn meet-distribute-once
  [expr]

  (if (multiplicative-expression? expr)
    (let [terms (rest expr)]
      (let [product-expressions (map
                                  (fn [i]
                                    (cons '* i))
                                  (apply
                                    enumerate-cartesian-product
                                    (map
                                      (fn [term]
                                        (if (not (coll? term))
                                          (list term)
                                          (rest term)))
                                      terms)))]
        (if (= (count product-expressions) 1)
          (first product-expressions)
          (cons '+ product-expressions))))
    expr))

; The main algorithm for producing meet normal forms of lattice expressions
(defn meet-distribute
  [expr]

  (cond
    ; if it is a singleton element then terminate and return
    (not (coll? expr)) expr

    ; a simple multiplicative expression cannot be distributed further
    ; so terminate the current algorithm and return
    (simple-multiplicative-expression? expr) expr

    ; in the other case we can try to perform meet distribution simplification
    (multiplicative-expression? expr)
    (let [current-simplification (simplify-lattice-expression (meet-distribute-once expr))]
      (meet-distribute current-simplification))

    ; additive expressions require simplification of all their terms
    (additive-expression? expr)
    (simplify-lattice-expression
      (cons
        '+
        (map
          (fn [i]
            (meet-distribute i))
          (rest expr))))))
