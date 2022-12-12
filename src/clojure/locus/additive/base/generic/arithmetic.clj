(ns locus.additive.base.generic.arithmetic
  (:refer-clojure :exclude [/ + - *])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]))

; Generic versions of ring operations
(defmulti add (fn [a b] [(type a) (type b)]))

(defmethod add :default
  [a b]

  (clojure.core/+ a b))

(defn +
  ([] 0)
  ([x] x)
  ([x y] (add x y))
  ([x y & more] (reduce add (add x y) more)))

(defmulti multiply (fn [a b] [(type a) (type b)]))

(defmethod multiply :default
  [a b]

  (clojure.core/* a b))

(defn *
  ([] 1)
  ([x] x)
  ([x y] (multiply x y))
  ([x y & more] (reduce multiply (multiply x y) more)))

(defmulti negate type)

(defmethod negate :default
  [a]

  (clojure.core/- a))

(defmulti reciprocal type)

(defmethod reciprocal :default
  [a]

  (clojure.core// a))

(defmulti subtract (fn [a b] [(type a) (type b)]))

(defmethod subtract :default
  [a b]

  (+ a (negate b)))

(defmulti divide (fn [a b] [(type a) (type b)]))

(defmethod divide :default
  [a b]

  (* a (reciprocal b)))

(defn -
  ([] 0)
  ([x] (negate x))
  ([x y] (subtract x y))
  ([x y & more]
   (- x (+ y (apply + more)))))

(defn /
  ([] 1)
  ([x] (reciprocal x))
  ([x y] (divide x y))
  ([x y & more]
   (/ x (* y (apply * more)))))

; Get the semiring of an element
(defmulti get-semiring type)