(ns locus.grothendieck.structure-sheaf.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.grothendieck.topology.core.object :refer :all]
            [locus.grothendieck.topology.core.morphism :refer :all]
            [locus.grothendieck.site.core.object :refer :all]
            [locus.grothendieck.sheaf.core.object :refer :all]
            [locus.grothendieck.topology.core.continuous-real-valued-function :refer :all]
            [locus.ring.core.protocols :refer :all]
            [locus.ring.core.object :refer :all]
            [locus.ring.core.morphism :refer :all]
            [locus.semiring.core.morphism :refer :all]))

; A structure sheaf is a functor F : C -> D from a source category C to a concrete category D,
; from which we can produce an underlying sheaf by factorisation with the functor of the
; concrete category G : D -> Sets.
(deftype StructureSheaf [site object-function morphism-function]
  StructuredDifunction
  (first-function [this] morphism-function)
  (second-function [this] object-function))

(defn underlying-sheaf
  [^StructureSheaf ss]

  (->Sheaf
    (.site ss)
    (fn [obj]
      (underlying-set (object-apply ss obj)))
    (fn [arrow]
      (underlying-function (morphism-apply ss arrow)))))

(defn sheaf-of-continuous-real-valued-functions
  [space]

  (topological-site space)
  (fn [obj]
    (ring-of-continuous-real-valued-functions obj))
  (fn [arrow]
    (let [[a b] arrow]
      (continuous-real-valued-function-ring-restriction-homomorphism a b))))

(defn sheaf-of-additive-groups
  [^StructureSheaf ss]

  (->Sheaf
    (.site ss)
    (fn [obj]
      (additive-semigroup obj))
    (fn [arrow]
      (morphism-of-additive-groups arrow))))

(defn sheaf-of-multiplicative-semigroups
  [^StructureSheaf ss]

  (->Sheaf
    (.site ss)
    (fn [obj]
      (multiplicative-semigroup obj))
    (fn [arrow]
      (morphism-of-multiplicative-semigroups arrow))))