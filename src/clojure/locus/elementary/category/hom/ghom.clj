(ns locus.elementary.category.hom.ghom
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.quiver.relation.binary.product :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.quiver.binary.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.quiver.base.core.protocols :refer :all]))

; The hom class of objects of a category
(deftype HomClass [category a b]
  clojure.lang.Seqable
  (seq [this]
    (seq
      (quiver-hom-class category a b)))

  clojure.lang.IFn
  (invoke [this arrow]
    (not
      (nil?
        (and
         ((morphisms category) arrow)
         (= (source-element category arrow) a)
         (= (target-element category arrow) b)))))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args))

  java.lang.Object
  (toString [this]
    (str "Hom class of morphisms from " a " to " b)))

(derive HomClass :locus.base.logic.core.set/universal)

(defmethod print-method HomClass [^HomClass v, ^java.io.Writer w]
  (.write w (.toString v)))

