(ns locus.elementary.dependency.nbijection.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.difunction.dibijection.object :refer :all]
            [locus.elementary.dependency.nset.object :refer :all]
            [locus.elementary.dependency.nfunction.object :refer :all])
  (:import (locus.elementary.difunction.dibijection.object Dibijection)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.dependency.nset.object NSet)
           (locus.elementary.dependency.nfunction.object NFunction)))

; Let Sets^(K_2 + K_2 + ...) be the topos of copresheaves over a two regular equivalence
; relation. Then copresheaves in this topos are equivalent to families of bijections.
; The objects of this topos have a dual purpose as objects of a topoi with their
; own internal logic as well as by being isomorphisms in the underlying groupoid of
; the n set topos of copresheaves over a discrete category Sets^n. Both of these
; dual purposes are implemented here.

(deftype NBijection [bijections]
  AbstractMorphism
  (source-object [this]
    (NSet. (map inputs bijections)))
  (target-object [this]
    (NSet. (map outputs bijections)))

  Invertible
  (inv [this]
    (NBijection.
      (map inv bijections))))

; Component morphisms of nth bijections
(defn nth-bijection
  [^NBijection func, i]

  (nth (.-bijections func) i))

; Components of nfunctions
(defmethod get-set NBijection
  [nfunction [i v]]

  (case i
    0 (get-set (source-object nfunction) v)
    1 (get-set (target-object nfunction) v)))

(defmethod get-function NBijection
  [nfunction [[i v] [j w]]]

  (case [i j]
    [0 0] (identity-function (inputs (nth-bijection nfunction v)))
    [1 1] (identity-function (outputs (nth-bijection nfunction v)))
    [0 1] (underlying-function (nth-bijection nfunction v))
    [1 0] (underlying-function (inv (nth-bijection nfunction v)))))

; The parent topos of an n-bijection
(defn nbijection-type
  [^NBijection func]

  (count (.-bijections func)))

; Convert collections of bijections into collections of functions
(defmethod to-nfunction NBijection
  [^NBijection coll]

  (let [n (count (.-bijections coll))]
    (NFunction.
      (map
        (fn [i]
          (underlying-function (nth-bijection coll i)))
        (range n)))))

; Ontology of classes of nbijections
(defmulti to-nbijection type)

(defmethod to-nbijection NBijection
  [^NBijection func] func)

(defmethod to-nbijection Dibijection
  [^Dibijection func]

  (NBijection.
    [(first-bijection func)
     (second-bijection func)]))

(defmethod to-nbijection Bijection
  [^Bijection func]

  (NBijection. [func]))

; Composition and identities in the underlying groupoid of the topos of copresheaves
(defn identity-nbijection
  [^NSet obj]

  (NBijection.
    (map
      identity-bijection
      (.colls obj))))

(defmethod compose* NBijection
  [a b]

  (let [n (count (.bijections a))]
    (NBijection.
      (map
        (fn [i]
          (compose (nth-bijection a i) (nth-bijection b i)))
        (range n)))))

; Products and coproducts in topoi of copresheaves over two regular thin groupoids
(defmethod product NBijection
  [& args]

  (NBijection.
    (let [n (nbijection-type (first args))]
      (map
        (fn [i]
          (apply product (map #(nth-bijection % i) args)))
        (range n)))))

(defmethod coproduct NBijection
  [& args]

  (NBijection.
    (let [n (nbijection-type (first args))]
      (map
        (fn [i]
          (apply coproduct (map #(nth-bijection % i) args)))
        (range n)))))

; Ontology of isomorphisms of nsets
(defn nbijection?
  [func]

  (= (type func) NBijection))