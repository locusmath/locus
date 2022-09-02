(ns locus.elementary.bijection.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.function.core.object :refer :all])
  (:import [locus.elementary.logic.base.core SeqableUniversal]
           [locus.elementary.function.core.object SetFunction]))

; Let K_2 be the thin category consisting of two objects and four morphisms. Then K_2 has
; an identity arrow for each of its two objects and one arrow going from each object
; to the other. Then Sets^(K_2) is the topos of bijections, which is the topos of
; copresheaves over this category. The output arrows of Sets^(K_2) are the function
; and the inverse function of a bijection. With this implementation, we distinguish
; bijections as elements of the topos Sets^(K_2) from invertible functions which are
; still elements of the topos Sets^(->).

(deftype Bijection [in out forward backward]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  StructuredDiset
  (first-set [this] in)
  (second-set [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  Invertible
  (inv [this]
    (Bijection. out in backward forward))
  
  clojure.lang.IFn
  (invoke [this obj]
    (forward obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Bijection :locus.elementary.function.core.protocols/bijection)

; Visualizer
(defmethod visualize Bijection
  [a]
  (visualize (underlying-relation a)))

; Conversion routines to turn things into bijections
(defmulti to-bijection type)

(defmethod to-bijection Bijection
  [bijection] bijection)

(defmethod to-bijection :locus.elementary.function.core.protocols/set-function
  [func]

  (if (not (invertible? func))
    (throw (new IllegalArgumentException))
    (->Bijection
      (inputs func)
      (outputs func)
      (fn [i]
        (func i))
      (fn [x]
        (first (fiber func x))))))

; Relational bijections
(defn relation-to-bijection
  [rel]

  (when (single-valued-binary-relation? rel)
    (Bijection.
      (relation-domain rel)
      (relation-codomain rel)
      (fn [x]
        (call rel x))
      (fn [y]
        (call (transpose rel) y)))))

(defmethod to-bijection :default
  [coll]

  (if (not (reversible-binary-relation? coll))
    (throw (new IllegalArgumentException))
    (relation-to-bijection coll)))

; The bijection builder method
(defn mapbn
  [coll]

  (when (distinct-seq? (vals coll))
    (Bijection.
     (set (keys coll))
     (set (vals coll))
     coll
     (apply
      array-map
      (apply concat (map reverse (seq coll)))))))

; Create a bijection from a simple pair
(defn pair-bijection
  [a b]

  (Bijection.
    #{a}
    #{b}
    (constantly b)
    (constantly a)))

; We can also get the bijection cardinality
(defn bijection-cardinality
  [func]
  
  (count (inputs func)))

; Composition
(defn compose-bijections
  ([f] f)
  ([f g]
   (Bijection.
    (inputs g)
    (outputs f)
    (comp (.forward f) (.forward g))
    (comp (.backward g) (.backward f))))
  ([f g & more] (reduce compose-functions (compose-functions f g) more)))

(defmethod compose* Bijection
  [a b] (compose-bijections a b))

; Identity
(defn identity-bijection
  [coll]

  (Bijection. coll coll identity identity))

; We can now define a product bijection
(defn bijection-product
  [& bijections]

  (Bijection.
   (apply cartesian-product (map inputs bijections))
   (apply cartesian-product (map outputs bijections))
   (fn [coll]
     (map-indexed
      (fn [i v]
        ((nth bijections i) v))
      coll))
   (fn [coll]
     (map-indexed
      (fn [i v]
        ((.backward (nth bijections i)) v))
      coll))))

(defn bijection-coproduct
  [& bijections]

  (Bijection.
   (apply cartesian-coproduct (map inputs bijections))
   (apply cartesian-coproduct (map outputs bijections))
   (fn [[i v]]
     (list i ((nth bijections i) v)))
   (fn [[i v]]
     (list i ((.backward (nth bijections i)) v)))))

(defmethod product Bijection
  [& args]

  (apply bijection-product args))

(defmethod coproduct Bijection
  [& args]

  (apply bijection-coproduct args))

; An attempt at creating power bijections
(defn power-bijection
  [func]

  (Bijection.
    (power-set (inputs func))
    (power-set (outputs func))
    (fn [coll]
      (set-image func coll))
    (fn [coll]
      (set-inverse-image func coll))))

; Restriction of bijections
(defn subbijection
  [bijection new-in new-out]

  (Bijection.
   new-in
   new-out
   (.forward bijection)
   (.backward bijection)))

(defn restrict-bijection
  [bijection new-in]

  (subbijection bijection new-in (set-image bijection new-in)))

; The critical issue now is that we must deal with the
; subobject and congruence lattices of a bijection.
(defn bijection-subobject?
  [bijection a b]

  (= (set-image bijection a) b))

(defn bijection-congruence?
  [bijection a b]

  (= (partition-image bijection a) b))

; Subalgebra lattices of bijections
(def number-of-subbijections
  (comp power-of-two bijection-cardinality))

(defn enumerate-subbijections
  [bijection]

  (map
   (fn [input-set]
     (list input-set (set-image bijection input-set)))
   (seqable-power-set (inputs bijection))))

(defn all-subbijections
  [bijection]

  (SeqableUniversal.
   (fn [[a b]]
     (bijection-subobject? bijection a b))
   (enumerate-subbijections bijection)
   {:count (number-of-subbijections bijection)}))

(defn subbijections
  [bijection]

  (map
    (fn [[a b]]
      (subbijection bijection a b))
    (enumerate-subbijections bijection)))

; Congruence lattices of bijections
(def number-of-bijection-congruences
  (comp bell-number bijection-cardinality))

(defn bijection-congruences
  [bijection]

  (map
   (fn [partition]
     (list partition (partition-image bijection partition)))
   (set-partitions (inputs bijection))))

(defn all-bijection-congruences
  [bijection]

  (SeqableUniversal.
    (fn [[a b]]
      (bijection-congruence? bijection a b))
    (bijection-congruences bijection)
    {:count (number-of-bijection-congruences bijection)}))

(defn quotient-bijection
  [bijection in-partition out-partition]

  (Bijection.
   in-partition
   out-partition
   (fn [in-part]
     (projection out-partition
                 (bijection (first in-part))))
   (fn [out-part]
     (projection in-partition
                 ((.backward bijection) (first out-part))))))

(defn quotient-bijections
  [bijection]

  (map
    (fn [[in-partition out-partition]]
      (quotient-bijection bijection in-partition out-partition))
    (bijection-congruences bijection)))

; Subalgebras and congruences in the topos of bijections
; are subalgebras and congruences in the topos of sets, where the
; bijection can be represented as a set by its underlying relation.
; so this leads to the following utilities to convert between the two forms.
(defn subrelation-to-subbijection
  [bijection rel]

  (list (relation-domain rel)
        (relation-codomain rel)))

(defn relation-partition-to-bijection-congruence
  [bijection partition]

  (list (set (map relation-domain partition))
        (set (map relation-codomain partition))))

; Ontology of bijection relations
(defn equal-bijections?
  [a b]

  (and
    (equal-universals? (inputs a) (inputs b))
    (equal-universals? (outputs a) (outputs b))
    (every?
      (fn [i]
        (= (a i) (b i)))
      (inputs a))))

; Ontology of bijections
(defn bijection?
  [bijection]

  (= (type bijection) Bijection))

(defn size-one-bijection?
  [bijection]

  (and (= (type bijection) Bijection)
       (= (bijection-cardinality bijection) 1)))

(defn size-two-bijection?
  [bijection]

  (and (= (type bijection) Bijection)
       (= (bijection-cardinality bijection) 2)))

(defn size-three-bijection?
  [bijection]

  (and (= (type bijection) Bijection)
       (= (bijection-cardinality bijection) 3)))

(defn size-four-bijection?
  [bijection]

  (and (= (type bijection) Bijection)
       (= (bijection-cardinality bijection) 4)))

(defn identity-bijection?
  [bijection]

  (and
    (bijection? bijection)
    (every?
      (fn [x]
        (= (bijection x) x))
      (inputs bijection))))

; Ontology of properties of bijections
(defn !=bijection
  [a b]

  (and
   (bijection? a)
   (bijection? b)
   (not= a b)))

(defn !=bijection-inputs
  [a b]

  (and
   (bijection? a)
   (bijection? b)
   (not= (inputs a) (inputs b))))

(defn !=bijection-outputs
  [a b]

  (and
   (bijection? a)
   (bijection? b)
   (not= (outputs a) (outputs b))))

(defn !=bijection-cardinality
  [a b]

  (and
   (bijection? a)
   (bijection? b)
   (not= (bijection-cardinality a) (bijection-cardinality b))))
