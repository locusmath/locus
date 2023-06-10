(ns locus.set.copresheaf.quiver.permutable.thin-morphism
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.vertexset :refer :all]
            [locus.set.square.core.morphism :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.core.morphism :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.object :refer :all]
            [locus.set.copresheaf.quiver.permutable.thin-object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import [locus.set.mapping.general.core.object SetFunction]
           (locus.set.copresheaf.quiver.permutable.thin_object ThinPermutableQuiver)))

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

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive MorphismOfThinPermutableQuivers :locus.set.copresheaf.structure.core.protocols/morphism-of-structured-permutable-quivers)

; Composition and identities in the category of thin permutable quivers
(defmethod compose* MorphismOfThinPermutableQuivers
  [a b]

  (MorphismOfThinPermutableQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (.func a) (.func b))))

(defmethod identity-morphism ThinPermutableQuiver
  [quiv] (MorphismOfThinPermutableQuivers. quiv quiv identity))
