(ns locus.elementary.quiver.unital.element
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.quiver.core.element :as qe])
  (:import (locus.elementary.quiver.core.element QuiverObject QuiverMorphism)))

; Identity morphisms of objects of unital quivers
(defmethod identity-morphism QuiverObject
  [^QuiverObject obj]

  (let [quiver (parent obj)
        object-member (member obj)
        identity-member (identity-morphism-of quiver object-member)]
    (QuiverMorphism.
      quiver
      identity-member)))
