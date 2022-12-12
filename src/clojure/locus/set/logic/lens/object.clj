(ns locus.set.logic.lens.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]))

; A lens is a set with a getter and a setter
(deftype Lens [coll getter setter]
  ConcreteObject
  (underlying-set [this]
    coll)

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
      first
      (fn [arg new-first]
        (list new-first (second arg))))))

(defn binary-product-second-lens
  [a b]

  (let [coll (product a b)]
    (Lens.
      coll
      second
      (fn [arg new-second]
        (list (first arg) new-second)))))

(defn nth-sequence-lens
  [n i]

  (Lens.
    (fn [coll]
      (and
        (seq? coll)
        (= (count coll) n)))
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
    #(get % key)
    (fn [arg val]
      (assoc arg key val))))

(defmethod compose* Lens
  [f g]

  (->Lens
    (underlying-set g)
    (fn [i]
      (f (g i)))
    ;todo
    (fn [arg val]
      (let [g-val (g arg)
            new-g-val (assocf f g-val val)]
        (assocf g arg new-g-val)))))