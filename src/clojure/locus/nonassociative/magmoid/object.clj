(ns locus.nonassociative.magmoid.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.nonassociative.magma.object :refer :all])
  (:import (locus.nonassociative.magma.object Magma)))

; A magmoid is a presheaf in the topos of compositional quivers.
(deftype Magmoid [quiver op]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] quiver)
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

(derive Magmoid :locus.set.copresheaf.structure.core.protocols/magmoid)

; Visualisation of magmoids
(defmethod visualize Magmoid
  [^Magmoid magmoid] (visualize (.-quiver magmoid)))

; Conversion routines
(defmulti to-magmoid type)

(defmethod to-magmoid Magmoid
  [^Magmoid obj] obj)

(defmethod to-magmoid Magma
  [^Magma magma]

  (->Magmoid
    (underlying-quiver magma)
    (.-op magma)))

; Products and coproducts of magmoids
(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/magmoid
  [& magmoids]

  (->Magmoid
    (apply coproduct (map underlying-quiver magmoids))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth magmoids i)]
          (list i (c (list v w))))))))

(defmethod product :locus.set.copresheaf.structure.core.protocols/magmoid
  [& magmoids]

  (->Magmoid
    (apply product (map underlying-quiver magmoids))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        magmoids))))

(defmethod dual :locus.set.copresheaf.structure.core.protocols/magmoid
  [magmoid]

  (->Magmoid (dual (underlying-quiver magmoid)) (comp magmoid reverse)))

; Get the endomorphism magma of an object of a magmoid
(defn endomorphism-magma
  [magmoid x]

  (->Magma
    (quiver-hom-class magmoid x x)
    magmoid))

; Subobjects of magmoids
(defn restrict-magmoid
  [magmoid new-morphisms new-objects]

  (->Magmoid
    (subquiver (underlying-quiver magmoid) new-morphisms new-objects)
    (fn [[a b]]
      (magmoid (list a b)))))

(defn wide-submagmoid
  [magmoid new-morphisms]

  (->Magmoid
    (wide-subquiver (underlying-quiver magmoid) new-morphisms)
    (fn [[a b]]
      (magmoid (list a b)))))

(defn full-submagmoid
  [magmoid new-objects]

  (->Magmoid
    (full-subquiver (underlying-quiver magmoid) new-objects)
    (fn [[a b]]
      (magmoid (list a b)))))

; Ontology of submagmoids
(defn submagmoid?
  [magmoid new-morphisms new-objects]

  (and
    (subquiver? (underlying-quiver magmoid) new-morphisms new-objects)
    (compositionally-closed-set? magmoid new-morphisms)))

; Ontology of magmoid congruences
(defn magmoid-congruence?
  [magmoid new-morphisms new-objects]

  (and
    (quiver-congruence? (underlying-quiver magmoid) new-morphisms new-objects)
    (compositional-congruence? magmoid new-morphisms)))

