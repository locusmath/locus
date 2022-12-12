(ns locus.set.copresheaf.bijection.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.mapping.invertible.function.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.con.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all])
  (:import [locus.set.logic.core.set SeqableUniversal]
           (locus.set.mapping.invertible.function.object InvertibleFunction)
           (clojure.lang IPersistentMap)))

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

  StructuredBijection
  (underlying-bijection [this] this)

  StructuredDiset
  (first-set [this] in)
  (second-set [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct
      [(inputs this) (outputs this)]))

  Invertible
  (inv [this]
    (Bijection. out in backward forward))

  clojure.lang.IFn
  (invoke [this obj]
    (forward obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Bijection :locus.set.copresheaf.structure.core.protocols/bijection)

; The elements of bijections
(defmethod get-set :locus.set.copresheaf.structure.core.protocols/bijection
  [bijection x]

  (case x
    0 (inputs bijection)
    1 (outputs bijection)))

(defmethod get-function :locus.set.copresheaf.structure.core.protocols/bijection
  [bijection [a b]]

  (case [a b]
    [0 0] (identity-function (inputs bijection))
    [1 1] (identity-function (outputs bijection))
    [0 1] (underlying-function bijection)
    [1 0] (underlying-function (inv bijection))))

; Convert bijections to invertible functions
(defmethod to-invertible-function Bijection
  [^Bijection func]

  (->InvertibleFunction (.-in func) (.-out func) (.-forward func) (.-backward func)))

; Convert relations to bijections
(defn relation-to-bijection
  [rel]

  (let [in (relation-domain rel)
        out (relation-codomain rel)
        reverse-rel (set (map reverse rel))
        func (into {} (map vec rel))
        inverse-func (into {} (map vec reverse-rel))]
    (->Bijection
      in
      out
      func
      inverse-func)))

; Conversion routines to turn things into bijections
(defmulti to-bijection type)

(defmethod to-bijection Bijection
  [bijection] bijection)

(defmethod to-bijection InvertibleFunction
  [^InvertibleFunction func]

  (Bijection. (.-in func) (.-out func) (.-forward func) (.-backward func)))

(defmethod to-bijection :locus.set.logic.structure.protocols/set-function
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

(defmethod to-bijection IPersistentMap
  [coll]

  (if (not (distinct-seq? (vals coll)))
    (throw (new IllegalArgumentException))
    (Bijection.
      (set (keys coll))
      (set (vals coll))
      coll
      (apply
        array-map
        (apply concat (map reverse (seq coll)))))))

(defmethod to-bijection :locus.set.logic.core.set/universal
  [coll]

  (relation-to-bijection coll))

; Composition and identities in the groupoid of bijections
(defmethod compose* Bijection
  [f g]

  (Bijection.
    (inputs g)
    (outputs f)
    (comp (.forward f) (.forward g))
    (comp (.backward f) (.backward g))))

(defn identity-bijection
  [coll]

  (->Bijection
    coll
    coll
    identity
    identity))

; Make a bijection from an invertible pair of functions
(defn make-bijection-by-function-pair
  [f g]

  (->Bijection
    (inputs g)
    (outputs g)
    g
    f))

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

; Images and inverses of sets by bijections
(defmethod image
  [:locus.set.copresheaf.structure.core.protocols/bijection :locus.set.logic.core.set/universal]
  [func coll]

  (set-image func coll))

(defmethod inverse-image
  [:locus.set.copresheaf.structure.core.protocols/bijection :locus.set.logic.core.set/universal]
  [func coll]

  (set-inverse-image func coll))

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

