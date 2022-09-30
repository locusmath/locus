(ns locus.structure.sheaf.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.grothendieck.topology.core.object :refer :all]
            [locus.grothendieck.topology.core.morphism :refer :all]
            [locus.grothendieck.site.core.object :refer :all]
            [locus.grothendieck.sheaf.core.object :refer :all]
            [locus.grothendieck.topology.core.continuous-real-valued-function :refer :all]
            [locus.additive.base.core.protocols :refer :all]
            [locus.additive.ring.core.object :refer :all]
            [locus.additive.ring.core.morphism :refer :all]
            [locus.additive.semiring.core.object :refer :all]
            [locus.additive.semiring.core.morphism :refer :all]))

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