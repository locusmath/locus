(ns locus.additive.base.core.protocols
  (:refer-clojure :exclude [/ + - *])
  (:require [locus.base.logic.core.set :refer :all :exclude [add]]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]))

; Additive structures can be established on categories by enriching them over the category CMon
; of commutative monoids or the category Ab of commutative groups. The former produces the
; category of semiringoids and the later produces the category of ringoids. Both of them
; can be understood in the context of horizontal categorification. The former is the horizontal
; categorification of a semiring, and the later is the horizontal categorification of a ring.

; Ontology of rings and semirings
(derive ::semiring :locus.base.logic.structure.protocols/structured-set)
(derive ::ring ::semiring)

(derive ::skew-semifield ::semiring)
(derive ::skew-field ::ring)
(derive ::skew-field ::ring)

; Ontology of the horizontal categorification of rings and semirings
(derive ::semiringoid :locus.elementary.copresheaf.core.protocols/semigroupoid)
(derive ::ringoid ::semiringoid)
(derive ::abelian-category ::ringoid)

; Predicates for rings, semirings, fields, and semifields
(defmulti semiring? type)

(defmethod semiring? :default
  [x] (isa? (type x) ::semiring))

(defmulti ring? type)

(defmethod ring? :default
  [x] (isa? (type x) ::ring))

(defn intrinsic-ring?
  [x] (isa? (type x) ::ring))

(defmulti skew-field? type)

(defmethod skew-field? :default
  [x] (isa? (type x) ::skew-field))

(defmulti skew-semifield? type)

(defmethod skew-semifield? :default
  [x] (isa? (type x) ::skew-semifield))

; Predicates for horizontal categorification of rings and semirings
(defmulti semiringoid? type)

(defmethod semiringoid? :default
  [x] (isa? (type x) ::semiringoid))

(defmulti ringoid? type)

(defmethod ringoid? :default
  [x] (isa? (type x) ::ringoid))

; Rings and semirings are like combinations of semigroups
(defmulti additive-semigroup type)

(defmulti multiplicative-semigroup type)

; Make a ring from a pair of semigroups by determining what the type
; of the semigroups is. This uses a pair of types in order to dispatch,
; so that it can be used to support rings, semirings, fields,
; and semifields as different types of abstractions of arithmetic.
(defmulti make-ring (fn [a b] [(type a) (type b)]))

; A semiring is like a category with a single object. So in the same way that a category
; has an accepted notion of a dual category, determined by reversing the order of multiplication
; there is also a corresponding notion of a dual of a ring or semiring determined
; by reversing the order of multiplication, while keeping the addition operation in tact.
; In other words, this is the dual of ringoids. For a commutative ring or semiring the dual
; operation should have no effect.
(defmethod dual ::semiring
  [semiring]

  (make-ring
    (additive-semigroup semiring)
    (dual (multiplicative-semigroup semiring))))

; Rings and semirings are algebras that are defined
; by collections of set functions.
(def addition-function
  (comp underlying-function additive-semigroup))

(def additive-identity-function
  (comp identity-element-function additive-semigroup))

(def additive-inverse-function
  (comp inverse-function additive-semigroup))

(def multiplication-function
  (comp underlying-function multiplicative-semigroup))

(def multiplicative-identity-function
  (comp identity-element-function multiplicative-semigroup))

; Testing for the presence of additive inverses is possible in the
; special cases where in there are rings described as semirings
(defmethod ring? ::semiring
  [semiring]

  (group? (additive-semigroup semiring)))

(defmethod skew-field? ::skew-semifield
  [semifield]

  (group? (additive-semigroup semifield)))

(defmethod skew-semifield? ::semiring
  [semifield]

  (group-with-zero? (multiplicative-semigroup semifield)))

(defmethod skew-field? ::ring
  [semiring]

  (group-with-zero? (multiplicative-semigroup semiring)))

(defmethod skew-field? ::semiring
  [semiring]

  (and
    (group? (additive-semigroup semiring))
    (group-with-zero? (multiplicative-semigroup semiring))))

; This is just a useful utility function for displaying the tables of finite
; rings and semirings. It should make it easier to handle interaction with
; rings and semirings in the preadditive categories system provided by Locus.
(defn display-tables
  [ring]

  (do
    (println "+")
    (display-table (additive-semigroup ring))
    (println "")
    (println "*")
    (display-table (multiplicative-semigroup ring))))