(ns locus.elementary.hom.generic.impl
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all]))

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

(defmethod print-method HomClass [^HomClass v, ^java.io.Writer w]
  (.write w (.toString v)))

