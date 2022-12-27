(ns locus.additive.field.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.commutative.monoid.arithmetic :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semifield.core.object :refer :all]
            [locus.additive.ring.core.object :refer :all]))

; A field is an arithmetic structure contain all relevant operations of
; addition, multiplication, subtraction, and division. Fields often emerge in
; commutative algebra from the quotients of commutative rings by maximal ideals,
; such as the unique maximal ideals of local rings, or by the field of fractions
; of an integral domain such as a quotient domain of a prime ideal.
(deftype SkewField [elems add mul]
  ConcreteObject
  (underlying-set [this] elems)

  StructuredDiset
  (first-set [this] elems)
  (second-set [this] #{0})

  StructuredQuiver
  (underlying-quiver [this] (singular-quiver elems 0))
  (source-fn [this] (constantly 0))
  (target-fn [this] (constantly 0))
  (transition [this obj] (list 0 0))

  ConcreteMorphism
  (inputs [this] (complete-relation elems))
  (outputs [this] elems)

  clojure.lang.IFn
  (invoke [this obj] (mul obj))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive SkewField :locus.additive.base.core.protocols/skew-field)

; Underlying multirelations for skew fields as ringoids
(defmethod underlying-multirelation SkewField
  [^SkewField field] (underlying-multirelation (underlying-quiver field)))

(defmethod underlying-relation SkewField
  [^SkewField field] (underlying-relation field))

(defmethod visualize SkewField
  [^SkewField field] (visualize (underlying-quiver field)))

; Additive and multiplicative components for skew fields
(defmethod additive-semigroup SkewField
  [^SkewField field]

  (.add field))

(defmethod multiplicative-semigroup SkewField
  [^SkewField field]

  (.mul field))

; A field should be constructed from an additive group and a multiplicative group with zero
(defmethod make-ring [:locus.set.copresheaf.structure.core.protocols/group,
                      :locus.set.copresheaf.structure.core.protocols/group-with-zero]
  [a b]

  (SkewField. (underlying-set a) a b))

; We also need to implement the modular multiplicative inverse
; The unique prime field of characteristic zero
(def qq
  (make-ring rational-addition rational-multiplication))
