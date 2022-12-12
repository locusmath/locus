(ns locus.set.tree.dimorphic-quiver.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]))

; A dimorphic quiver is simply a quiver with a set of objects O and two different sets of morphisms
; ton objects in O. Equivalently, they are presheaves over the category C consisting of three
; objects: representing the object set and the two morphism sets, and four non-identity arrows
; representing the first source, second source, first target, and second target functions.
(deftype DimorphicQuiver [first-quiver second-quiver])

(derive DimorphicQuiver :locus.set.logic.structure.protocols/copresheaf)

; Constructors for dimorphic quivers
(defn dimorphic-quiver
  [quiver1 quiver2]

  (DimorphicQuiver. quiver1 quiver2))

(defn constant-dimorphic-quiver
  [coll]

  (dimorphic-quiver (constant-quiver coll) (constant-quiver coll)))

; Components of dimorphic quivers
(defn first-quiver
  [^DimorphicQuiver quiver]

  (.-first_quiver quiver))

(defn second-quiver
  [^DimorphicQuiver quiver]

  (.-second_quiver quiver))

(defn dimorphic-quiver-target
  [^DimorphicQuiver quiver]

  (objects (first-quiver quiver)))

(defn first-morphisms
  [^DimorphicQuiver quiver]

  (morphisms (first-quiver quiver)))

(defn second-morphisms
  [^DimorphicQuiver quiver]

  (morphisms (second-quiver quiver)))

(defn first-source-function
  [^DimorphicQuiver quiver]

  (source-function (first-quiver quiver)))

(defn second-source-function
  [^DimorphicQuiver quiver]

  (source-function (second-quiver quiver)))

(defn first-target-function
  [^DimorphicQuiver quiver]

  (target-function (first-quiver quiver)))

(defn second-target-function
  [^DimorphicQuiver quiver]

  (target-function (second-quiver quiver)))

; Successor quivers of dimorphic quivers
(defmethod successor-quiver DimorphicQuiver
  [^DimorphicQuiver quiver, i]

  (cond
    (= i '()) (identity-function (dimorphic-quiver-target quiver))
    (= i '(0)) (first-quiver quiver)
    (= i '(1)) (second-quiver quiver)))

; Given a dimorphic quiver its two morphism sets can be collapsed into a single one to get a
; single combined quiver with the coproduct of the two morphisms sets as its new morphism set
; and sharing the same set of objects as the dimorphic quiver.
(defmethod to-quiver DimorphicQuiver
  [^DimorphicQuiver quiver]

  (let [all-morphisms (coproduct (first-morphisms quiver) (second-morphisms quiver))]
    (->Quiver
      all-morphisms
      (dimorphic-quiver-target quiver)
      (fn [[i v]]
        (case i
          0 (source-element (first-quiver quiver) v)
          1 (source-element (second-quiver quiver) v)))
      (fn [[i v]]
        (case i
          0 (target-element (first-quiver quiver) v)
          1 (target-element (second-quiver quiver) v))))))

; Generic conversion routines for dimorphic quivers
(defmulti to-dimorphic-quiver type)

(defmethod to-dimorphic-quiver DimorphicQuiver
  [^DimorphicQuiver quiver] quiver)

; Relational multimethods implemented for dimorphic quivers
(defmethod underlying-multirelation DimorphicQuiver
  [^DimorphicQuiver quiver]

  (add (underlying-multirelation (first-quiver quiver)) (underlying-multirelation (second-quiver quiver))))

(defmethod underlying-relation DimorphicQuiver
  [^DimorphicQuiver quiver]

  (union (underlying-relation (first-quiver quiver)) (underlying-relation (second-quiver quiver))))

(defmethod visualize DimorphicQuiver
  [^DimorphicQuiver quiver]

  (visualize (underlying-multirelation quiver)))

; Products and coproducts in the topos of dimorphic quivers
(defmethod product DimorphicQuiver
  [& quivers]

  (->DimorphicQuiver
    (apply product (map first-quiver quivers))
    (apply product (map second-quiver quivers))))

(defmethod coproduct DimorphicQuiver
  [& quivers]

  (->DimorphicQuiver
    (apply coproduct (map first-quiver quivers))
    (apply coproduct (map second-quiver quivers))))

; Ontology of dimorphic quivers
(defn dimorphic-quiver?
  [obj]

  (= (type obj) DimorphicQuiver))
