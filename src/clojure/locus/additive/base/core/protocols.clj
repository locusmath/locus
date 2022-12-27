(ns locus.additive.base.core.protocols
  (:refer-clojure :exclude [/ + - *])
  (:require [locus.set.logic.core.set :refer :all :exclude [add]]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]))

; Categories are sets of morphisms between objects where the morphisms are equipped with a
; multiplication operation *. As a consequence, it is always possible to multiply two
; morphisms of a category, but that is only half of the story. In the larger context of
; semirings, ringoids, and similar structures equipped with an addition operation +
; it is possible to both add and multiply the morphisms of such enriched categories.
; So we say that rings are ringods with a single object and semirings are semiringoids
; with a single object.

(derive ::semiringoid :locus.set.copresheaf.structure.core.protocols/semigroupoid)
(derive ::ringoid ::semiringoid)
(derive ::abelian-category ::ringoid)
(derive ::semiring ::semiringoid)
(derive ::ring ::semiring)
(derive ::skew-semifield ::semiring)
(derive ::skew-field ::skew-semifield)
(derive ::skew-field ::ring)

; Rings and semirings are constructed from the combination of two different semigroups: an addition
; semigroup and a multiplication semigroup. It is useful for us to be able to access either of
; these two semigroups individually. We can do that now by using the additive-semigroup and
; multiplicative-semigroup methods.

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
; by reversing the order of multiplication, while keeping the addition operation intact.
; In other words, this is the dual of ringoids. For a commutative ring or semiring the dual
; operation should have no effect.

(defmethod dual ::semiring
  [semiring]

  (make-ring
    (additive-semigroup semiring)
    (dual (multiplicative-semigroup semiring))))

; Rings and semirings are algebras that are defined by collections of set functions.
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

; Endomorphism algebras
; A semimodule is associated to an endomorphism semiring, and a module
; is associated to an endomorphism ring
(defmulti endomorphism-algebra type)

; Predicates for ringoids and semiringoids
(defmulti semiringoid? type)

(defmethod semiringoid? :default
  [x] (isa? (type x) ::semiringoid))

(defmulti ringoid? type)

(defmethod ringoid? :default
  [x] (isa? (type x) ::ringoid))

; Predicates for single object ringoids and semiringoids
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