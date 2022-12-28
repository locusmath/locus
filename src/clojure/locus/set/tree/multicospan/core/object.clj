(ns locus.set.tree.multicospan.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all])
  (:import (locus.set.mapping.general.core.object SetFunction)))

; A multicospan is a copresheaf in the topos Sets^{[n,1]} consisting of n functions with a
; common target. These generalize cospans which have only a single target. As objects of a
; topos, multicospans have all products, coproducts, and other topos related functionality
; available for them.
(deftype Multicospan [coll funcs])

(derive Multicospan :locus.set.logic.structure.protocols/copresheaf)

; Components of multicospans
(defn multicospan-type
  [^Multicospan cospan]

  (count (.-funcs cospan)))

(defn multicospan-target
  [^Multicospan multicospan]

  (.-coll multicospan))

(defn nth-multicospan-source
  [^Multicospan multicospan, i]

  (inputs (nth (.-funcs multicospan) i)))

(defn nth-multicospan-function
  [^Multicospan multicospan, i]

  (nth (.-funcs multicospan) i))

; Constructors for special types of multicospans
(defn multicospan
  [& funcs]

  (->Multicospan
    (outputs (first funcs))
    (vec funcs)))

(defn constant-multicospan
  [coll n]

  (Multicospan.
    coll
    (repeat n (identity-function coll))))

(defn singleton-multicospan
  [& elems]

  (let [last-elem (last elems)]
    (->Multicospan
      #{last-elem}
      (vec
        (map
          (fn [i]
            (mapfn
              {(nth elems i) last-elem}))
          (range (dec (count elems))))))))

(defn coproduct-multicospan
  [& colls]

  (let [target (apply coproduct colls)]
    (->Multicospan
      target
      (vec
        (map-indexed
          (fn [i coll]
            (inclusion-function
              (set
               (map
                 (fn [elem]
                   (list i elem))
                 coll))
              target))
          colls)))))

; Convert various objects into multicospans
(defmulti to-multicospan type)

(defmethod to-multicospan Multicospan
  [^Multicospan multicospan] multicospan)

(defmethod to-multicospan :locus.set.logic.structure.protocols/set-function
  [func]

  (Multicospan. (outputs func) [func]))

; Convert multicospans into functions by collapsing all their inputs using a coproduct
(defmethod to-function Multicospan
  [^Multicospan multicospan]

  (->SetFunction
    (apply
      coproduct
      (map
        (fn [i]
          (nth-multicospan-source multicospan i))
        (range (multicospan-type multicospan))))
    (multicospan-target multicospan)
    (fn [[i v]]
      ((nth-multicospan-function multicospan i) v))))

; Get the successor quiver of a cell in a multicospan
(defmethod successor-quiver Multicospan
  [^Multicospan multicospan, i]

  (cond
    (empty? i) (identity-function (multicospan-target multicospan))
    :else (let [n (first i)]
            (nth-multicospan-function multicospan i))))

; Implement multicospans as copresheaves
(defmethod get-set Multicospan
  [^Multicospan multicospan, i]

  (if (empty? i)
    (multicospan-target multicospan)
    (nth-multicospan-source multicospan (first i))))

(defmethod get-function Multicospan
  [^Multicospan multicospan, [source target]]

  (if (= source target)
    (identity-function (get-set multicospan source))
    (let [i (first source)]
      (nth-multicospan-function multicospan i))))

; Products and coproducts in topoi of multicospan copresheaves
(defmethod coproduct Multicospan
  [& multicospans]

  (let [n (multicospan-type (first multicospans))]
    (->Multicospan
     (apply coproduct (map multicospan-target multicospans))
     (vec
       (map
        (fn [i]
          (apply
            coproduct
            (map
              (fn [multicospan]
                (nth-multicospan-function multicospan i))
              multicospans)))
        (range n))))))

(defmethod product Multicospan
  [& multicospans]

  (let [n (multicospan-type (first multicospans))]
    (->Multicospan
      (apply product (map multicospan-target multicospans))
      (vec
        (map
         (fn [i]
           (apply
             product
             (map
               (fn [multicospan]
                 (nth-multicospan-function multicospan i))
               multicospans)))
         (range n))))))

; Visualisation of multicospans
(defmethod visualize Multicospan
  [^Multicospan multicospan]

  (let [size (multicospan-type multicospan)
        [p v] (generate-copresheaf-data
                (into
                  {}
                  (map
                    (fn [i]
                      [i (if (= i size)
                           (multicospan-target multicospan)
                           (nth-multicospan-source multicospan i))])
                    (range (inc size))))
                (set
                  (map
                    (fn [i]
                      (list i size (nth-multicospan-function multicospan i)))
                    (range size))))]
    (visualize-clustered-digraph* "BT" p v)))

; Ontology of multicospans
(defn multicospan?
  [obj]

  (= (type obj) Multicospan))

