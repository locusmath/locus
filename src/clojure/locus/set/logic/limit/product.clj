(ns locus.set.logic.limit.product
  (:require [clojure.set]
            [locus.set.logic.core.set :refer :all])
  (:import [locus.set.logic.core.set Universal SeqableUniversal]))

; Let Sets be the topos of sets. Recall that every topos is associated with products and coproducts.
; This file handles the formation of these products and coproducts of sets.

; Cartesian products
(defn enumerate-cartesian-product
  [& colls]

  (letfn [(place-system [coll]
            (fn [j]
              (map
                (fn [i]
                  (mod (quot j (apply * (take i coll)))
                       (nth coll i)))
                (range (count coll)))))]
    (let [sorted-colls (map (comp vec seq) colls)
          coll-counts (map count colls)
          func (place-system coll-counts)]
      (map
        (fn [i]
          (let [current-coordinate (func i)]
            (seq
              (map-indexed
               (fn [first-index second-index]
                 (nth (nth sorted-colls first-index) second-index))
               current-coordinate))))
        (range (apply * coll-counts))))))

(defn cartesian-product-classifier
  [& colls]

  (fn [coll]
    (and
      (seq? coll)
      (= (count coll) (count colls))
      (every?
        (fn [i]
          ((nth colls i) (nth coll i)))
        (range (count colls))))))

(defn cartesian-product
  [& colls]

  (if (every? seqable-universal? colls)
    (set (apply enumerate-cartesian-product colls))
    (apply cartesian-product-classifier colls)))

; The category theoretic dual operation to the cartesian product is the
; coproduct of sets, which we can define here by turning a coproduct of
; sets into a numerically indexed relation.
(defn enumerate-cartesian-coproduct
  [& colls]

  (apply
    concat
    (map-indexed
      (fn [i v]
        (set
          (map
            (fn [j]
              (list i j))
            v)))
      colls)))

(defn cartesian-coproduct-classifier
  [& colls]

  (let [n (count colls)]
    (fn [[i x]]
      (and
        (natural-number? i)
        (< i n)
        ((nth colls i) x)
        true))))

(defn cartesian-coproduct
  [& colls]

  (if (every? seqable-universal? colls)
    (set (apply enumerate-cartesian-coproduct colls))
    (apply cartesian-coproduct-classifier colls)))

; Multimethods for dealing with products and coproducts in categories
(defmulti product
          (fn [& args] (type (first args))))

(defmethod product :default
  [& args]

  (apply cartesian-product args))

(defmulti coproduct
          (fn [& args] (type (first args))))

(defmethod coproduct :default
  [& args]

  (apply cartesian-coproduct args))

; Ontology of cartesian products and coproducts
(derive ::cartesian-product :locus.set.logic.core.set/universal)
(derive ::cartesian-coproduct :locus.set.logic.core.set/universal)

; Cartesian products
(deftype CartesianProduct [colls]
  clojure.lang.Seqable
  (seq [this]
    (apply enumerate-cartesian-product colls))

  clojure.lang.Counted
  (count [this]
    (apply * (map count colls)))

  java.lang.Object
  (toString [this]
    (if (empty? colls)
      (.toString #{})
      (apply
        str
        (butlast
          (interleave
            colls
            (repeat (count colls) " × "))))))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (seq? arg)
      (= (count arg) (count colls))
      (every?
        (fn [i]
          ((nth colls i) (nth arg i)))
        (range (count colls)))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive CartesianProduct ::cartesian-product)

(defmethod print-method CartesianProduct [^CartesianProduct v, ^java.io.Writer w]
  (.write w ^String (.toString v)))

; Intersection method for nary cartesian products
(defmethod intersection* #{CartesianProduct}
  [p1 p2]

  (let [a (.colls p1)
        b (.colls p2)]
    (if (not= (count a) (count b))
      #{}
      (let [new-colls (map
                        (fn [i]
                          (intersection (nth a i) (nth b i)))
                        (range (count a)))
            nonempty? (every?
                        (fn [i]
                          (not (empty? i)))
                        new-colls)]
        (if nonempty?
          (CartesianProduct. new-colls)
          #{})))))

; Cartesian coproducts
(deftype CartesianCoproduct [colls]
  clojure.lang.Seqable
  (seq [this]
    (apply enumerate-cartesian-coproduct colls))

  clojure.lang.Counted
  (count [this]
    (apply + (map count colls)))

  java.lang.Object
  (toString [this]
    (if (empty? colls)
      (.toString #{})
      (apply
        str
        (butlast
          (interleave
            colls
            (repeat (count colls) " + "))))))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (coll? arg)
      (= (count arg) 2)
      (let [[x y] arg]
        (and
          (number? x)
          (< x (count colls))
          (boolean ((nth colls x) y))))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive CartesianCoproduct ::cartesian-coproduct)

(defmethod print-method CartesianCoproduct [^CartesianCoproduct v, ^java.io.Writer w]
  (.write w ^String (.toString v)))

; Cartesian powers:
; Cartesian powers are distinguished by the fact that all their components are equal to one another.
; As a consequence, they produce a different type of functional behaviour than what occurs when using
; ordinary cartesian products. In the derive hierarchy, they are classified as special types of
; cartesian products. The vertices multimethod is overriden for quick handling of members
; of the cartesian power class.

; Mathematically a cartesian power can always be described as a set S^n. In this manner, given
; two cartesian powers S^n and T^m then their intersection is the empty set unless m = n.
; Otherwise, it is equal to U^n where U is equal to the intersection of S and T. In this way,
; we have have the means by which we can define an overloaded intersection method for
; members of the cartesian power class.
(defn enumerate-cartesian-power
  [coll n]

  (apply enumerate-cartesian-product (repeat n coll)))

(defn cartesian-power
  [coll n]

  (apply cartesian-product (repeat n coll)))

(deftype CartesianPower [coll n]
  clojure.lang.Seqable
  (seq [this]
    (enumerate-cartesian-power coll n))

  clojure.lang.Counted
  (count [this]
    (int (.pow (BigInteger/valueOf (count coll)) n)))

  java.lang.Object
  (toString [this]
    (let [superscript {\0 "⁰"
                       \1 "¹"
                       \2 "²"
                       \3 "³"
                       \4 "⁴"
                       \5 "⁵"
                       \6 "⁶"
                       \7 "⁷"
                       \8 "⁸"
                       \9 "⁹"}
          superscript-string (apply
                               str
                               (map superscript (.toString n)))]
      (str coll superscript-string)))

  clojure.lang.IFn
  (invoke [this arg]
    (and
      (seq? arg)
      (= (count coll) n)
      (every? coll arg)))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive CartesianPower :locus.set.logic.limit.product/cartesian-product)

(defmethod print-method CartesianPower [^CartesianPower v, ^java.io.Writer w]
  (.write w ^String (.toString v)))

(defmethod intersection* #{CartesianPower}
  [^CartesianPower a, ^CartesianPower b]

  (if (not= (.n a) (.n b))
    #{}
    (let [common-arity (.n a)]
      (CartesianPower. (intersection (.coll a) (.coll b)) common-arity))))

; Vertices are a multimethod now applicable to any number
; of relational predicate data types.
(defmulti vertices
          (fn [a] (type a)))

(defmethod vertices CartesianProduct
  [^CartesianProduct rel]

  (apply union (.colls rel)))

(defmethod vertices CartesianPower
  [^CartesianPower rel] (.coll rel))

(defmethod vertices :default
  [rel]

  (apply
    union
    (for [i rel
          :when (seq? i)]
      (set i))))

; This is a synonym for the vertices method
(defn relation-to-set
  [rel]

  (vertices rel))

; Seqable cartesian powers
(defn seqable-cartesian-product
  [& colls]

  (SeqableUniversal.
    (intersection
      seq?
      (fn [coll]
        (and
          (= (count coll) (count colls))
          (every?
            (fn [i]
              ((nth colls i) (nth coll i)))
            (range (count colls))))))
    (apply enumerate-cartesian-product colls)
    {:count (apply * (map count colls))}))

(defn seqable-cartesian-power
  [coll n]

  (apply seqable-cartesian-product (repeat n coll)))