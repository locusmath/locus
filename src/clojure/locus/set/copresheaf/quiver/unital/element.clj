(ns locus.set.copresheaf.quiver.unital.element
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.set.quiver.binary.element.object :as qe]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.element.object QuiverObject QuiverMorphism)))

; Identity morphisms of objects of unital quivers
(defmethod identity-morphism QuiverObject
  [^QuiverObject obj]

  (let [quiver (parent obj)
        object-member (member obj)
        identity-member (identity-morphism-of quiver object-member)]
    (QuiverMorphism.
      quiver
      identity-member)))
