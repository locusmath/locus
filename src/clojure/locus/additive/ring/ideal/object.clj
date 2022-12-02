(ns locus.additive.ring.ideal.object
  (:refer-clojure :exclude [+ * - /])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.quiver.base.core.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.base.generic.arithmetic :refer :all]
            [locus.additive.base.core.protocols :refer :all]))

; Let R be a ring. Then an ideal of R is simply a subset of R which is simultaneously an
; additive subgroup and a multiplicative two sided semigroup ideal. In this file, we
; support ideals with the Ideal class which is defined by an ideal and its set of
; generators. On top of this ideal class we also introduce generic arithmetic operations
; of addition and multiplication, so that ideals can be treated as objects of a semiring.

; First class support for ideals of rings
(deftype Ideal [ring gens])

; Ideals can be added and multiplied together
(defmethod add [Ideal Ideal]
  [^Ideal i, ^Ideal j]

  (Ideal. (.ring i) (union (.gens i) (.gens j))))

(defmethod multiply [Ideal Ideal]
  [^Ideal i, ^Ideal j]

  (Ideal.
    (.ring i)
    (set
      (for [x (.gens i)
            y (.gens j)]
       (apply-semigroup (multiplicative-semigroup (.ring i)) (list x y))))))

(defn zero-ideal
  [ring]

  (Ideal. ring #{}))

(defn ideal-classifier
  [ring]

  (fn [i]
    (and
      (= (type i) Ideal)
      (= (.ring i) ring))))

(defmethod get-semiring Ideal
  [i]

  (let [ring (.ring i)
        classifier (ideal-classifier ring)]
    (make-ring
      (->Monoid
        classifier
        (fn [[a b]]
          (add a b))
        (zero-ideal ring))
      (->Semigroup
        classifier
        (fn [[a b]]
          (multiply a b))))))

