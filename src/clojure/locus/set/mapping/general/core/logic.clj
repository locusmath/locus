(ns locus.set.mapping.general.core.logic
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.sub.core.object :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.sub.mapping.function :refer :all]
            [locus.set.mapping.function.core.functor :refer :all])
  (:import (locus.set.square.core.morphism SetSquare)))

; Two types of truth values
(deftype InputTruth [val]
  Object
  (toString [this]
    (case val
      0 "in-false"
      1/2 "in-middle"
      1 "in-true")))

(defmethod print-method InputTruth [^InputTruth v ^java.io.Writer w]
  (.write w (.toString v)))

(deftype OutputTruth [val]
  Object
  (toString [this]
    (case val
      0 "out-false"
      1 "out-true")))

(defmethod print-method OutputTruth [^OutputTruth v ^java.io.Writer w]
  (.write w (.toString v)))

(defn truth-number
  [obj]

  (cond
    (= (type obj) InputTruth) (.val ^InputTruth obj)
    (= (type obj) OutputTruth) (.val ^OutputTruth obj)))

(defn truth-type
  [obj]

  (cond
    (= (type obj) InputTruth) 0
    (= (type obj) OutputTruth) 1))

; truth values
(def in-false (InputTruth. 0))
(def in-middle (InputTruth. 1/2))
(def in-true (InputTruth. 1))
(def in-truth-values
  (list in-false in-middle in-true))

(def out-false (OutputTruth. 0))
(def out-true (OutputTruth. 1))
(def out-truth-values
  (list out-false out-true))

(defn input-truth
  [num]

  (case num
    0 in-false
    1/2 in-middle
    1 in-true))

(defn output-truth
  [num]

  (case num
    0 out-false
    1 out-true))

; View functions
(defn view-transformation
  [func]

  (prn
    (str
      (truth-number (func in-false))
      " "
      (truth-number (func in-middle))
      " "
      (truth-number (func in-true))
      " | "
      (truth-number (func out-false))
      " "
      (truth-number (func out-true)))))

(defn view-connective
  [func]

  (doseq [i in-truth-values]
    (doseq [j in-truth-values]
      (print (truth-number (func i j)) " "))
    (print "\n"))
  (print "\n")
  (print "----")
  (print "\n")
  (doseq [i out-truth-values]
    (doseq [j out-truth-values]
      (print (truth-number (func i j)) " "))
    (print "\n")))

; operators
(def constant-true
  {in-false in-true
   in-middle in-true
   in-true in-true
   out-false out-true
   out-true out-true})

(def constant-middle
  {in-false in-middle
   in-middle in-middle
   in-true in-middle
   out-false out-true
   out-true out-true})

(def constant-false
  {in-false in-false
   in-middle in-false
   in-true in-false
   out-false out-false
   out-true out-false})

(def negate
  {in-false in-true
   in-middle in-false
   in-true in-false
   out-false out-true
   out-true out-false})

(def middle
  {in-false in-false
   in-middle in-true
   in-true in-middle
   out-false out-false
   out-true out-true})

(def weak-negate
  {in-false in-true
   in-middle in-true
   in-true in-middle
   out-false out-true
   out-true out-true})

(defn logical-identity
  [a]  a)

(defn double-negate
  [a]

  (negate (negate a)))

(defn middle-of-negation
  [x]

  (middle (negate x)))

(defn middle-of-double-negation
  [x]

  (middle (double-negate x)))

(defn weak-double-negation
  [x]

  (weak-negate (weak-negate x)))

(defn double-weak-negation-of-negation
  [x]

  (weak-negate (weak-negate (negate x))))

(defn double-weak-negation-of-middle
  [x]

  (weak-negate (weak-negate (middle x))))

(defn weak-negation-of-middle
  [x]

  (weak-negate (middle x)))

(defn weak-negation-of-negation
  [x]

  (weak-negate (negate x)))

(def unary-operatives
  #{constant-true
     constant-middle
     constant-false
     middle
     negate
     weak-negate
     logical-identity
     double-negate
     middle-of-negation
     middle-of-double-negation
     weak-double-negation
     double-weak-negation-of-negation
     double-weak-negation-of-middle
     weak-negation-of-middle
     weak-negation-of-negation})

; Logical connectives
(defn p*
  [a b]

  (if (not= (truth-type a) (truth-type b))
    (throw (new IllegalArgumentException "Type error"))
    a))

(defn q*
  [a b]

  (if (not= (truth-type a) (truth-type b))
    (throw (new IllegalArgumentException "Type error"))
    b))

(defn make-logical-connective
  [in-func out-func]

  (fn [a b]
    (if (not= (truth-type a) (truth-type b))
      (throw (new IllegalArgumentException "Type error"))
      (cond
        (= (truth-type a) (truth-type b) 0) (input-truth (in-func (.val a) (.val b)))
        (= (truth-type a) (truth-type b) 1) (output-truth (out-func (.val a) (.val b)))))))

(def conjunction
  (make-logical-connective min min))

(def disjunction
  (make-logical-connective max max))

; determine the validity of implication in the topos of functions
(def implication
  (make-logical-connective
    (fn [a b]
      (if (<= a b)
        1
        (if (and (= a 1) (= b 1/2))
          1/2
          0)))
    (fn [a b]
      (if (<= a b)
        1
        0))))

(defn coimplication
  [a b]

  (implication b a))

(defn logical-equality
  [a b]

  (conjunction
    (implication a b)
    (implication b a)))

; Tautology tests for the sierpinski topos
(defn tautology?
  [n formula]

  (and
    (every?
      (fn [coll]
        (= in-true (apply formula coll)))
      (cartesian-power (set in-truth-values) n))
    (every?
      (fn [coll]
        (= out-true (apply formula coll)))
      (cartesian-power (set out-truth-values) n))))

; the law of noncontradiction is valid in the sierpinski topos
(defn noncontradiction
  [p]

  (negate (conjunction p (negate p))))

; de morgans laws are valid
(defn negated-union
  [a b]

  (negate (disjunction a b)))

(defn intersection-of-negations
  [a b]

  (conjunction (negate a) (negate b)))

(defn negated-intersection
  [a b]

  (negate (conjunction a b)))

(defn union-of-negations
  [a b]

  (disjunction (negate a) (negate b)))

; Modus ponens is valid
(defn modus-ponens
  [p q]

  (implication
    (conjunction
      (implication p q)
      p)
    q))

(defn modus-tollens
  [p q]

  (implication
    (conjunction
      (implication p q)
      (negate q))
    (negate q)))

; The hypothetical syllogism is true
(defn hypothetical-syllogism
  [p q r]

  (implication
    (conjunction
      (implication p q)
      (implication q r))
    (implication p r)))

; The disjunctive syllogism seems to work out
(defn disjunctive-syllogism
  [p q]

  (implication
    (conjunction
      (disjunction p q)
      (negate p))
    q))

; The disjunction introduction works without an issue
(defn disjunction-introduction
  [p q]

  (implication
    p
    (disjunction p q)))

; The simplification law is fine as well
(defn simplification-law
  [p q]

  (implication
    (conjunction p q)
    p))

; No reason exportation shouldn't hold
(defn exportation
  [p q r]

  (logical-equality
    (implication p (implication q r))
    (implication (conjunction p q) r)))

; There is nothing to stop us from using negation introduction
(defn negation-introduction
  [p q]

  (implication
    (conjunction
      (implication p q)
      (implication p (negate q)))
    (negate p)))

; Disjunction elimination works fine
(defn disjunction-elimination
  [p q r]

  (implication
    (reduce
      conjunction
      (list
        (implication p q)
        (implication r q)
        (disjunction p r)))
    q))

; To reconstruct the logical implication method in the sierpinski topos
; we have an alternative method, which deals with the tragic problem
; of the lack of the material implication law: we simply have to
; use ~p or q or (?p and ?q) which means that we have to be able to
; include the case wherein there is the excluded middle, the common
; middles between the two of them. But I think that once we deal with that
; we will actually get around the issue of the implication laws,
; which means that we will finally have a good means of dealing with
; symbolic logic in the sierpinski topos

; The material implication law fails to hold
(defn material-implication-law
  [p q]

  (logical-equality
    (implication p q)
    (disjunction (negate p) q)))

; Test for the transposition law: the transposition law is
; yet another thing that fails, it simply does not work
(defn transposition-law
  [p q]

  (logical-equality
    (implication p q)
    (implication (negate q) (negate p))))

; Again the admirable consequence law is related to the law of excluded
; middle so consequentia mirablis is simply not going to work
(defn admirable-consequence-law
  [p]

  (implication
    (implication (negate p) p)
    p))

; Pierces law also fails to hold, because it is a substitute for
; the law of excluded middle for those logics that only use implication
(defn pierces-law
  [p q]

  (implication
    (implication
      (implication p q)
      p)
    p))

; The failure of the resolution law is a direct consequence
; of the logical failure of material implication, so there are
; some limits to what we can do in the sierpinski topos,
; the key thing here is that the material implication law
; simply does not hold
(defn resolution
  [p q r]

  (implication
    (conjunction
      (disjunction p q)
      (disjunction (negate p) r))
    (implication q r)))

; -------------
; Here are some more logical laws that hold in general
(defn biconditional-elimination
  [p q]

  (implication
    (logical-equality p q)
    (implication p q)))

(defn biconditional-introduction
  [p q]

  (implication
    (conjunction
      (implication p q)
      (implication q p))
    (logical-equality p q)))

(defn constructive-dilemma
  [p q r s]

  (implication
    (reduce
      conjunction
      (list
        (implication p q)
        (implication r s)
        (disjunction p r)))
    (disjunction q s)))

(defn destructive-dilemma
  [p q r s]

  (implication
    (reduce
      conjunction
      (list
        (implication p q)
        (implication r s)
        (disjunction (negate q) (negate s))))
    (disjunction (negate p) (negate r))))

(defn absorption-law
  [p q]

  (implication
    (implication p q)
    (implication p (conjunction p q))))

; A logical law
(defn import-export
  [p q r]

  (logical-equality
    (implication p (implication q r))
    (implication (conjunction p q) r)))

(defn freges-theorem
  [p q r]

  (implication
    (implication
      p
      (implication q r))
    (implication
      (implication p q)
      (implication p r))))

; Consensus law
; According to this the consensus law fails
; So eventually I would like to know what that is all about
(defn consensus-law
  [x y z]

  (logical-equality
    (reduce
      disjunction
      (list
        (conjunction x y)
        (conjunction (negate x) y)
        (conjunction y z)))
    (disjunction
      (conjunction x y)
      (conjunction (negate x) z))))

; The working of the object of truth values
(defn get-output-truth
  [in-truth-value]

  (if (= in-truth-value in-false)
    out-false
    out-true))

; Truth pairs
(def in-truth-pairs
  (cartesian-power (set in-truth-values) 2))

(def out-truth-pairs
  (cartesian-power (set out-truth-values) 2))

(defn truelike?
  [val]

  (or (= val in-true) (= val out-true)))

(defn symdiff
  [a b]

  (or (and a (not b))
      (and (not a) b)))

(defn get-classified-pairs
  [func]

  (list
    (set
      (filter
        (fn [[a b]]
          (func (truelike? a) (truelike? b)))
        in-truth-pairs))
    (set
      (filter
        (fn [[a b]]
          (func (truelike? a) (truelike? b)))
        out-truth-pairs))))

(defn connective-set-pair-interior
  [[in-set out-set]]

  (list
    (set
      (filter
        (fn [[a b]]
          (contains?
            out-set
            (list (get-output-truth a) (get-output-truth b))))
        in-set))
    out-set))

(defn connective-set-pair-closure
  [[in-set out-set]]

  (list
    in-set
    (union
      out-set
      (set
        (map
          (fn [[a b]]
            (list (get-output-truth a) (get-output-truth b)))
          in-set)))))

(defn connective-set-pair-operator
  [[in-set out-set]]

  (fn [a b]
    (if (= (truth-type a) (truth-type b) 0)
      (if (contains? in-set (list a b))
        in-true
        (let [v (list (get-output-truth a) (get-output-truth b))]
          (if (contains? out-set v)
            in-middle
            in-false)))
      (if (contains? out-set (list a b))
        out-true
        out-false))))

(defn strong-connective
  [func]

  (connective-set-pair-operator
    (connective-set-pair-interior
      (get-classified-pairs func))))

(defn weak-connective
  [func]

  (connective-set-pair-operator
    (connective-set-pair-closure
      (get-classified-pairs func))))

; Logical operatives
(def classical-false
  (fn [a b] false))

(def classical-true
  (fn [a b] true))

(def classical-and
  (fn [a b] (and a b)))

(def classical-or
  (fn [a b] (or a b)))

(defn classical-first
  [a b] a)

(defn classical-second
  [a b] b)

; Logical operatives not lattice based
(def classical-xor
  (fn [a b]
    (or (and a (not b))
        (and (not a) b))))

(def classical-nxor
  (fn [a b] (= a b)))

(def classical-nand
  (fn [a b] (not (and a b))))

(def classical-nor
  (fn [a b] (not (or a b))))

(defn classical-not-first
  [a b] (not a))

(defn classical-not-second
  [a b] (not b))

(defn classical-implication
  [a b] (or (not a) b))

(defn classical-coimplication
  [a b] (or a (not b)))

(defn classical-not-implication
  [a b] (not (or (not a) b)))

(defn classical-not-coimplication
  [a b] (not (or a (not b))))

; Weak negation with the middle

; get the middle of the conjunction or the disjunction
(defn middle-of-conjunction
  [a b]

  (middle (conjunction a b)))

(defn middle-of-disjunction
  [a b]

  (middle (disjunction a b)))

(defn disjunction-of-middles
  [a b]

  (disjunction (middle a) (middle b)))

(defn conjunction-of-middles
  [a b]

  (conjunction (middle a) (middle b)))

(defn midcon1
  [a b]

  (reduce
    conjunction
    (list
      (disjunction (middle a) (middle b))
      (negate (negate a))
      (negate (negate b)))))

(defn midcon2
  [a b]

  (reduce
    disjunction
    (list
      (conjunction (middle a) (middle b))
      (conjunction a (middle b))
      (conjunction (middle a) b))))

(defn middisj2
  [a b]

  (reduce
    disjunction
    (list
      (conjunction (middle a) (negate b))
      (conjunction (negate a) (middle b))
      (conjunction (middle a) (middle b)))))

(defn middisj1
  [a b]

  (reduce
    conjunction
    (list
      (disjunction (middle a) (middle b))
      (weak-negate a)
      (weak-negate b))))

; The universal image is different from the existence image
(defn universal-image
  [func coll]

  (set
    (filter
      (fn [i]
        (every?
          (fn [j]
            (contains? coll j))
          (fiber func i)))
      (outputs func))))

(def m
  (->SetSquare
    (mapfn {0 0, 1 1, 2 2, 3 3, 4 4, 5 5})
    (mapfn {0 0, 1/2 1, 1 1})
    (mapfn {0 1/2, 1 0, 2 1, 3 0, 4 1/2, 5 0})
    (mapfn {0 1, 1 0, 2 1, 3 0, 4 1, 5 0})))

; quantifiers as adjoints
; this is simply not going to work, so some other notion must
; be defined in order for this to work well
(defn set-pair-universal-image
  [diamond [s t]]

  (let [sp (universal-image (input-set-function diamond) s)
        tp (universal-image (output-set-function diamond) t)]
    (subalgebra-interior (target-object diamond) sp tp)))

(defn all-set-pair-universal-images
  [diamond]

  (set
    (map
      (fn [[a b]]
        (set-pair-universal-image diamond [a b]))
      (all-subalgebras (source-object diamond)))))

; Get all efficient set pairs of a function
(defn efficient-set-pairs
  [func]

  (set
    (map
      (fn [coll]
        (vec (list (set-inverse-image func coll) coll)))
      (power-set (function-image func)))))

(defn efficient-set-pairs-covering
  [func]

  (let [im (function-image func)]
    (set
      (mapcat
        (fn [coll]
          (let [remaining-elements (difference im coll)]
            (map
              (fn [remaining-element]
                (list
                  (vec
                    (list (set-inverse-image func coll) coll))
                  (let [parent-coll (conj coll remaining-element)]
                    (vec
                      (list (set-inverse-image func parent-coll) parent-coll)))))
              remaining-elements)))
        (power-set im)))))

; Test for lawvere topologies
(defn equal-connectives?
  [n a b]

  (tautology?
    n
    (fn [& args]
      (logical-equality
        (apply a args)
        (apply b args)))))

(defn truth-preserving?
  [op]

  (equal-connectives? 1 constant-true (comp op constant-true)))

(defn idempotent-operative?
  [op]

  (equal-connectives? 1 op (comp op op)))

(defn conjunction-preserving?
  [op]

  (equal-connectives?
    2
    (fn [a b]
      (conjunction (op a) (op b)))
    (fn [a b]
      (op (conjunction a b)))))

(defn lawvere-topology?
  [op]

  (and
    (truth-preserving? op)
    (idempotent-operative? op)
    (conjunction-preserving? op)))

; internal sub and con
(defn internal-sub-function
  [func]

  (let [in (set (map vec (all-subalgebras truth-function)))
        out (power-set (outputs func))]
    (->SetFunction
      in
      out
      (fn [pair]
        (second pair)))))

(defn internal-con-function
  [func]

  (let [in (set (map vec (all-congruences func)))
        out (set-partitions (outputs func))]
    (->SetFunction
      in
      out
      (fn [pair]
        (second pair)))))

