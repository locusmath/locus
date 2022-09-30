(ns locus.elementary.group.term.signed-list
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.group.term.signed-multiset :refer :all]))

; Let G be a free group over a set of generators S, then we say that the elements of G
; are lists of elements of S that also can include the data of signs which describe
; rather or not a given element is inverted. This leads to a special data structure,
; implemented here for describing elements of free groups.

(deftype SignedList
  [elems inverses]

  Object
  (toString [this]
    (str
      "("
      (apply
       str
       (map
         (fn [i]
           (str (nth elems i)
                (if (nth inverses i) "⁻¹" "")
                " "))
         (range (count elems))))
      ")"))

  Invertible
  (inv [this]
    (SignedList. (reverse elems) (map not (reverse inverses)))))

(defmethod print-method SignedList [^SignedList v, ^java.io.Writer w]
  (.write w (.toString v)))

; Conversion methods
(defn to-signed-list
  [coll]

  (SignedList.
    coll
    (repeat (count coll) false)))

; Utility methods for signed lists
(defn signed-nth
  [^SignedList coll, n]

  (nth (.elems coll) n))

(defn signed-nth-inverse
  [^SignedList coll, n]

  (nth (.inverses coll) n))

(defn signed-length
  [^SignedList coll]

  (count (.elems coll)))

(defn signed-indices
  [^SignedList coll]

  (set
    (filter
      (fn [i]
        (nth (.inverses coll) i))
      (range (count (.elems coll))))))

(defn signed-list-values
  [^SignedList coll]

  (set (.elems coll)))

; Signed list multiplicity
(defn signed-list-multiplicity
  [coll elem]

  (apply
    +
    (for [i (range (signed-length coll))
          :when (= (nth (.elems coll) i) elem)]
      (if (true? (nth (.inverses coll) i))
        -1
        1))))

; Take part of a signed list
(defn signed-take
  [coll n]

  (SignedList.
    (take n (.elems coll))
    (take n (.inverses coll))))

(defn signed-drop
  [coll n]

  (SignedList.
    (drop n (.elems coll))
    (drop n (.inverses coll))))

; We need some way of simplifying group words
(defn first-cancellable-index
  [signed-list]

  (let [coll (.elems signed-list)
        inverses (.inverses signed-list)]
    (first
     (filter
       (fn [i]
         (and
           (= (nth coll i) (nth coll (inc i)))
           (not= (nth inverses i) (nth inverses (inc i)))))
       (range (dec (count coll)))))))

(defn cancel-list-index
  [coll i]

  (concat
    (take i coll)
    (drop (+ i 2) coll)))

(defn cancel-signed-list-index
  [coll i]

  (SignedList.
    (cancel-list-index (.elems coll) i)
    (cancel-list-index (.inverses coll) i)))

(defn simplify-signed-list
  [coll]

  (loop [remaining-list coll]
    (let [i (first-cancellable-index remaining-list)]
      (if (not (nil? i))
        (recur
         (cancel-signed-list-index remaining-list i))
        remaining-list))))

(defn concatenate-signed-lists
  [a b]

  (simplify-signed-list
    (SignedList.
     (concat (.elems a) (.elems b))
     (concat (.inverses a) (.inverses b)))))

; A necessary predicate for dealing with signed lists
(defn signed-list?
  [coll]

  (= (type coll) SignedList))

; Get the underlying signed multiset of a signed list as they would appear if the
; free group term was commutative
(defn underlying-signed-multiset
  [coll]

  (letfn [(remove-zeros [coll]
            (select-keys
              coll
              (filter
                (fn [key]
                  (not (zero? (get coll key))))
                (keys coll))))]
    (->SignedMultiset
      (remove-zeros
       (loop [multiplicities {}
              current-coll coll]
         (if (zero? (signed-length current-coll))
           multiplicities
           (recur
             (let [current-element (signed-nth current-coll 0)
                   current-sign (if (signed-nth-inverse current-coll 0) -1 1)
                   current-multiplicity (if (nil? (get multiplicities current-element))
                                          current-sign
                                          (+ current-sign (get multiplicities current-element)))]
               (assoc multiplicities current-element current-multiplicity))
             (SignedList.
               (rest (.elems current-coll))
               (rest (.inverses current-coll))))))))))
