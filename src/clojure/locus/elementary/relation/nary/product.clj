(ns locus.elementary.relation.nary.product
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]))

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

(defmethod print-method CartesianProduct [^CartesianProduct v, ^java.io.Writer w]
  (.write w ^String (.toString v)))

(defmethod seqable-universal? CartesianProduct
  [rel] true)

; The vertices of the cartesian product are the union of its constructor arguments
(defmethod vertices CartesianProduct
  [rel]

  (apply union (.colls rel)))

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

; Cartesian powers
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

(defmethod print-method CartesianPower [^CartesianPower v, ^java.io.Writer w]
  (.write w ^String (.toString v)))

(defmethod seqable-universal? CartesianProduct
  [^CartesianPower rel] true)

(defmethod vertices CartesianPower
  [^CartesianPower rel] (.coll rel))

(defmethod intersection* #{CartesianPower}
  [^CartesianPower a, ^CartesianPower b]

  (if (not= (.n a) (.n b))
    #{}
    (let [common-arity (.n a)]
      (CartesianPower. (intersection (.coll a) (.coll b)) common-arity))))

