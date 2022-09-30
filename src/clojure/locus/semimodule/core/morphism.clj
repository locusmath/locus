(ns locus.semimodule.core.morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.action.core.protocols :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.action.global.morphism :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.semigroup.monoid.morphism :refer :all]
            [locus.elementary.semigroup.core.morphism :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.group.core.morphism :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.ring.core.morphism :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semiring.core.morphism :refer :all]
            [locus.semimodule.core.object :refer :all]
            [locus.semimodule.core.utils :refer :all]))

; Morphisms in categories of semimodules
(deftype SemimoduleMorphism [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  ConcreteMorphism
  (inputs [this] (underlying-set source))
  (outputs [this] (underlying-set target))

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Identities and composition in categories of semimodules
(defmethod identity-morphism Semimodule
  [semimodule]

  (SemimoduleMorphism. semimodule semimodule identity))

(defmethod compose* SemimoduleMorphism
  [a b]

  (SemimoduleMorphism.
    (source-object b)
    (target-object a)
    (comp (.func a) (.func b))))

; The morphic part of the topos valued functor to the topos of MSets of a module category
(defn morphism-of-scalar-multiplication-actions
  [morphism]

  (->EquivariantMap
    (to-mset (source-object morphism))
    (to-mset (target-object morphism))
    (.func morphism)))

; Semimodule hom monoids
(defn semimodule-hom-class
  [a b]

  (fn [morphism]
    (and
      (= (type morphism) SemimoduleMorphism)
      (= (source-object morphism) a)
      (= (target-object morphism) b))))

(defn add-semimodule-morphisms
  [m1 m2]

  (SemimoduleMorphism.
    (source-object m1)
    (target-object m1)
    (fn [x]
      (let [add (additive-semigroup (target-object m1))]
        (add [(m1 x) (m2 x)])))))

(defn zero-semimodule-morphism
  ([source]
   (zero-semimodule-morphism source source))
  ([source target]
   (let [add (.semigroup target)
         id (first (identity-elements add))]
     (SemimoduleMorphism.
       source
       target
       (fn [x] id)))))

(defn additive-hom-monoid
  [a b]

  (->Monoid
    (semimodule-hom-class a b)
    (fn [[a b]]
      (add-semimodule-morphisms a b))
    (zero-semimodule-morphism a b)))

; Endomorphism algebras of semimodules, which are naturally semirings
(defmethod endomorphism-algebra Semimodule
  [semimodule]

  (make-ring
    (additive-hom-monoid semimodule semimodule)
    (->Monoid
      (semimodule-hom-class semimodule semimodule)
      (fn [[a b]]
        (compose a b))
      (identity-morphism semimodule))))

; Every semimodule induces a homomorphism of semirings to an endomorphism algebra
(defn action-ring-homomorphism
  [^Module semimodule]

  (let [out-semimodule (to-semimodule (additive-semigroup semimodule))]
    (->SemiringMorphism
      (.ring semimodule)
      (endomorphism-algebra out-semimodule)
      (fn [action]
        (->SemimoduleMorphism
          out-semimodule
          out-semimodule
          (fn [i]
            (apply-action semimodule action i)))))))



