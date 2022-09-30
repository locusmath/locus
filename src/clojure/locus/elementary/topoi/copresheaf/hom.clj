(ns locus.elementary.topoi.copresheaf.hom
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]))

; The hom copresheaf of a category C
(defn hom-copresheaf
  [category source-object]

  (->Copresheaf
    category
    (fn [obj]
      (quiver-hom-class category source-object obj))
    (fn [arrow]
      ; arrow : x -> y
      (let [x (source-element category arrow)
            y (target-element category arrow)]
        (->SetFunction
         (quiver-hom-class category source-object x)
         (quiver-hom-class category source-object y)
         (fn [morphism]
           (category (list arrow morphism))))))))
