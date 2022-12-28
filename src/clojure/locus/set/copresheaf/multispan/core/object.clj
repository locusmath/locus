(ns locus.set.copresheaf.multispan.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.general.core.util :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.copresheaf.incidence.core.object :refer :all]))

; A multispan is a copresheaf of sets in the topos Sets^{[1,n]} consisting of n functions with a
; common source. They generalize incidence structures to define flags that have more than
; two components in them, or multivalued incidence structures.
(deftype Multispan [coll funcs])

(derive Multispan :locus.set.logic.structure.protocols/copresheaf)

; Functions for multispan copresheaves
(defn multispan-type
  [^Multispan multispan]

  (count (.-funcs multispan)))

(defn multispan-flags
  [^Multispan multispan]

  (.-coll multispan))

(defn nth-multispan-component
  [^Multispan multispan, i]

  (outputs (nth (.-funcs multispan) i)))

(defn nth-multispan-function
  [^Multispan multispan, i]

  (nth (.-funcs multispan) i))

; Constructors for multispan copresheaves
(defn multispan
  [& funcs]

  (Multispan.
    (inputs (first funcs))
    funcs))

(defn constant-multispan
  [coll n]

  (Multispan.
    coll
    (repeat n (identity-function coll))))

(defn singleton-multispan
  [& vals]

  (let [first-elem (first vals)]
    (->Multispan
      #{first-elem}
      (map
        (fn [i]
          (pair-function first-elem (nth vals i)))
        (range 1 (count vals))))))

; Conversion functions for multispan copresheaves
(defmulti to-multispan type)

(defmethod to-multispan Multispan
  [^Multispan multispan] multispan)

(defmethod to-multispan :locus.set.logic.structure.protocols/set-function
  [func]

  (->Multispan (inputs func) [func]))

; Copresheaf theoretic methods for multispans
(defmethod get-set Multispan
  [^Multispan multispan, i]

  (if (zero? i)
    (multispan-flags multispan)
    (nth-multispan-component multispan (dec i))))

(defmethod get-function Multispan
  [^Multispan multispan, [i j]]

  (if (= i j)
    (identity-function (get-object multispan i))
    (nth-multispan-function multispan (dec j))))

; Products and coproducts of multispans
(defmethod coproduct Multispan
  [& multispans]

  (let [n (multispan-type (first multispans))]
    (->Multispan
     (apply coproduct (map multispan-flags multispans))
     (vec
       (map
        (fn [i]
          (apply coproduct (map #(nth-multispan-function % i) multispans)))
        (range n))))))

(defmethod product Multispan
  [& multispans]

  (let [n (multispan-type (first multispans))]
    (->Multispan
      (apply product (map multispan-flags multispans))
      (vec
        (map
         (fn [i]
           (apply product (map #(nth-multispan-function % i) multispans)))
         (range n))))))

; Visualisation of multispan copresheaves
(defmethod visualize Multispan
  [^Multispan multispan]

  (let [size (multispan-type multispan)
        [p v] (generate-copresheaf-data
                (into
                  {}
                  (map
                    (fn [i]
                      [i (if (zero? i)
                           (multispan-flags multispan)
                           (nth-multispan-component multispan (dec i)))])
                    (range (inc size))))
                (set
                  (map
                    (fn [i]
                      (list 0 i (nth-multispan-function multispan (dec i))))
                    (range 1 (inc size)))))]
    (visualize-clustered-digraph* "BT" p v)))

; Ontology of multispan copresheaves
(defn multispan?
  [obj]

  (= (type obj) Multispan))