(ns locus.elementary.topoi.nset.nbijection
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.difunction.core.object :refer :all]
            [locus.elementary.dibijection.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.topoi.nset.object :refer :all]
            [locus.elementary.topoi.nset.morphism :refer :all])
  (:import (locus.elementary.dibijection.core.object Dibijection)
           (locus.elementary.bijection.core.object Bijection)
           (locus.elementary.topoi.nset.object NSet)
           (locus.elementary.topoi.nset.morphism NFunction)))

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

(defn nth-bijection
  [^NBijection func, i]

  (nth (.-bijections func) i))

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