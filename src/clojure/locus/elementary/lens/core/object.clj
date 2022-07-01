(ns locus.elementary.lens.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.lens.core.lens-type :refer :all]))

; The setter must take the form (in,new val) -> in
(deftype Lens [in-set out-set getter setter]
  ConcreteObject
  (underlying-set [this] in-set)

  ConcreteMorphism
  (inputs [this] in-set)
  (outputs [this] out-set)

  clojure.lang.IFn
  (invoke [this arg]
    (getter arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; We need some way to turn local effects into global ones
(defmulti globalize type)

; Methods that make effective use of the lens functionality by allowing for
; the theory of local actions to take form
(defn assocf
  [lens obj val]

  ((.setter lens) obj val))

(defn zap
  [lens obj func]

  (assocf lens obj (func (lens obj))))

; We need to create lens structures for product types
(defn product-lens
  [colls n]

  (Lens.
    (apply cartesian-product colls)
    (nth colls n)
    #(nth % n)
    (fn [arg x]
      (concat
        (take n arg)
        (list x)
        (drop (inc n) arg)))))

(defn binary-product-first-lens
  [a b]

  (let [coll (product a b)]
    (Lens.
      coll
      a
      first
      (fn [arg new-first]
        (list new-first (second arg))))))

(defn binary-product-second-lens
  [a b]

  (let [coll (product a b)]
    (Lens.
      coll
      a
      second
      (fn [arg new-second]
        (list (first arg) new-second)))))

; Create a basic lens of the nth slot of a sequence
(defn nth-sequence-lens
  [n i]

  (Lens.
    (fn [coll]
      (and
        (seq? coll)
        (= (count coll) n)))
    entity?
    #(nth % i)
    (fn [arg x]
      (concat
        (take i arg)
        (list x)
        (drop (inc i) arg)))))

; Get a lens to refer to a key within a map
(defn map-key-lens
  [key]

  (Lens.
    map?
    entity?
    #(get % key)
    (fn [arg val]
      (assoc arg key val))))

