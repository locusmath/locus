(ns locus.elementary.quiver.permutable.thin-morphism
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertexset :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.permutable.thin-object :refer :all])
  (:import [locus.base.function.core.object SetFunction]
           (locus.elementary.quiver.permutable.thin_object ThinPermutableQuiver)))

; Morphisms in the category of thin permutable quivers, which is embedded in the topos
; of permutable quivers, represented as copresheaves.
(deftype MorphismOfThinPermutableQuivers [source-quiver target-quiver func]  AbstractMorphism
  (source-object [this] source-quiver)
  (target-object [this] target-quiver)

  ConcreteMorphism
  (inputs [this] (objects source-quiver))
  (outputs [this] (objects target-quiver))

  StructuredDifunction
  (first-function [this]
    (SetFunction.
      (morphisms source-quiver)
      (morphisms target-quiver)
      (fn [[a b]]
        (list (func a) (func b)))))
  (second-function [this]
    (SetFunction.
      (objects source-quiver)
      (objects target-quiver)
      func))

  StructuredMorphismOfQuivers
  (underlying-morphism-of-quivers [this]
    this)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MorphismOfThinPermutableQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-permutable-quivers)

; Composition and identities in the category of thin permutable quivers
(defmethod compose* MorphismOfThinPermutableQuivers
  [a b]

  (MorphismOfThinPermutableQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (.func a) (.func b))))

(defmethod identity-morphism ThinPermutableQuiver
  [quiv] (MorphismOfThinPermutableQuivers. quiv quiv identity))
