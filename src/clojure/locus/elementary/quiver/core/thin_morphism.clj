(ns locus.elementary.quiver.core.thin-morphism
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
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.morphism :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all])
  (:import (locus.base.function.core.object SetFunction)
           (locus.elementary.quiver.core.thin_object ThinQuiver)))

; A morphism of thin quivers can essentially be determined entirely by its
; vertex function. Then the edge function of the morphism can be determined
; uniquely by the product of the vertex function with itself. This makes the
; subcategory of thin quivers essentially equivalent to the category of digraphs.
(deftype MorphismOfThinQuivers [source-quiver target-quiver func]
  AbstractMorphism
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

(derive MorphismOfThinQuivers :locus.elementary.copresheaf.core.protocols/morphism-of-structured-quivers)

; We have a conversion function just in case
(defn to-morphism-of-quivers
  [morphism]

  (->MorphismOfQuivers
    (source-object morphism)
    (target-object morphism)
    (first-function morphism)
    (target-function morphism)))

; Composition and identities in the topos of quivers
(defmethod compose* MorphismOfThinQuivers
  [a b]

  (MorphismOfThinQuivers.
    (source-object b)
    (target-object a)
    (compose-functions (.func a) (.func b))))

(defmethod identity-morphism ThinQuiver
  [quiv] (MorphismOfThinQuivers. quiv quiv identity))

; We need to be able to define induced inclusions
(defn induced-inclusion
  [morphism]

  (inclusion-function
    (underlying-relation (source-object morphism))
    (inflate-relation
      (objects (source-object morphism))
      (underlying-relation (target-object morphism))
      morphism)))
