(ns locus.set.copresheaf.indexed.family.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (clojure.lang IPersistentMap IPersistentVector)))

; Let C be a discrete category on a set S, then we say that a copresheaf over C is the same thing
; as a family of sets indexed on S.
(deftype IndexedFamily [coll func])

; The index set of an indexed family is the set of objects of its discrete index category
(defn index-set
  [^IndexedFamily family]

  (.-coll family))

; Create an indexed family naturally from a hash map valued in sets
(defn indexed-family
  [coll]

  (IndexedFamily. (set (keys coll)) coll))

; Convert objects into indexed families
(defmulti to-indexed-family type)

(defmethod to-indexed-family IndexedFamily
  [^IndexedFamily family] family)

(defmethod to-indexed-family IPersistentMap
  [coll]

  (indexed-family coll))

(defmethod to-indexed-family IPersistentVector
  [coll]

  (->IndexedFamily
    (->Upto (count coll))
    (fn [i]
      (nth coll i))))

(defmethod to-indexed-family :locus.set.logic.core.set/universal
  [coll]

  (IndexedFamily.
    #{0}
    (constantly coll)))

; Get the underlying indexed family of a copresheaf
(defn underlying-indexed-family
  [coll]

  (->IndexedFamily
    (objects (index coll))
    (fn [i]
      (get-set coll i))))

; Take an indexed family and get a Clojure persistent hash map from it
(defn indexed-family-map
  [^IndexedFamily family]

  (let [coll (.-coll family)
        ordered-coll (seq coll)]
    (zipmap
      ordered-coll
      (map (.-func family) ordered-coll))))

; Indexed families are like set-valued functions
(defmethod to-function IndexedFamily
  [^IndexedFamily family]

  (let [coll (.-coll family)]
    (->SetFunction
      coll
      (set (map (.-func family) coll))
      coll)))

; Getters for the set elements of an indexed family of sets
(defmethod get-set IndexedFamily
  [^IndexedFamily family, obj]

  ((.-func family) obj))

(defmethod get-function IndexedFamily
  [^IndexedFamily family, [a b]]

  (identity-function (get-set family a)))

; Products and coproducts of indexed families
(defmethod product IndexedFamily
  [& families]

  (IndexedFamily.
    (index-set (first families))
    (fn [i]
      (apply
        product
        (map
          (fn [indexed-family]
            (get-set indexed-family i))
          families)))))

(defmethod coproduct IndexedFamily
  [& families]

  (IndexedFamily.
    (index-set (first families))
    (fn [i]
      (apply
        coproduct
        (map
          (fn [indexed-family]
            (get-set indexed-family i))
          families)))))

; Ontology of indexed families of sets
(defn indexed-family?
  [family]

  (= (type family) IndexedFamily))
