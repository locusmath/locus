(ns locus.algebra.category.hom.ghom
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]))

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

(derive HomClass :locus.set.logic.core.set/universal)

(defmethod print-method HomClass [^HomClass v, ^java.io.Writer w]
  (.write w (.toString v)))

