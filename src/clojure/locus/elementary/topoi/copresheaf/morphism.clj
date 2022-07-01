(ns locus.elementary.topoi.copresheaf.morphism
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.category.core.natural-transformation :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all])
  (:import (locus.elementary.topoi.copresheaf.object Copresheaf)))

; Morphisms in a topos of copresheaves
; Let C be a category and Sets^C its topos of copresheaves. Then a morphism of copresheaves
; is simply a morphism in this topos.
(deftype MorphismOfCopresheaves
  [source-functor target-functor func]

  AbstractMorphism
  (source-object [this] source-functor)
  (target-object [this] target-functor)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

; Convert morphism of copresheaves into copresheaves
(defmulti to-copresheaf type)

(defmethod to-copresheaf MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (let [source-functor (.-source_functor morphism)
        target-functor (.-target_functor morphism)
        func (.-func morphism)
        index-category (source-object source-functor)]
    (Copresheaf.
      (double-category index-category)
      (fn [[i v]]
        (case i
          0 (source-functor v)
          1 (target-functor v)))
      (fn [[i v]]
        (case i
          0 (source-functor v)
          1 (target-functor v)
          2 (let [src (source-element index-category v)]
              (compose (target-functor v) (func src))))))))

; Composition and identities in the topos of copresheaves
(defmethod identity-morphism Copresheaf
  [copresheaf]

  (MorphismOfCopresheaves.
    copresheaf
    copresheaf
    identity-morphism))

(defmethod compose* MorphismOfCopresheaves
  [a b]

  (MorphismOfCopresheaves.
    (source-object b)
    (target-object a)
    (fn [obj]
      (compose (a obj) (b obj)))))

; Conversion mechanisms for morphisms of copresheaves
(defmethod to-natural-transformation MorphismOfCopresheaves
  [^MorphismOfCopresheaves morphism]

  (->NaturalTransformation
    (to-functor (source-object morphism))
    (to-functor (target-object morphism))
    (.func morphism)))


