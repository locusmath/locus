(ns locus.set.copresheaf.topoi.bicopresheaf.hom
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.copresheaf.topoi.copresheaf.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.set.copresheaf.topoi.bicopresheaf.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

; Every category is uniquely associated with a bicopresheaf Hom: C^op x C -> Sets.
(defn hom-bicopresheaf
  [category]

  (->Bicopresheaf
    (dual category)
    category
    (fn [[a b]]
      (quiver-hom-class category a b))
    (fn [[input-action output-action]]
      (let [[a b] (transition category input-action)
            [c d] (transition category output-action)]
        (->SetFunction
          (quiver-hom-class category b c)
          (quiver-hom-class category a d)
          (fn [morphism]
            (category
              (list
                output-action
                (category (list morphism input-action))))))))))