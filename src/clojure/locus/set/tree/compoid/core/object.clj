(ns locus.set.tree.compoid.core.object
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
            [locus.set.quiver.ternary.core.object :refer :all]
            [locus.set.tree.two-quiver.core.object :refer :all]
            [locus.set.tree.two-quiver.path.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]))

; The topos of composition quivers is the topos of presheaves over the compositional quiver index
; category, which is a category generated by five morphisms between three objects. Compositional
; quivers are noteworthy for providing the presheaf theoretic account of categories. They form
; a topos that includes categories as well as their immediate generalisations: semigroupoids,
; magmoids, groupoids, partial magmoids, and so on. They are so generalized that they include
; epi-mono factorisations so that by this topos you can form epi-mono factorisations of functors
; between two categories using an intermediate composition quiver determined by a quotient
; and a subobject.

; The modus operandi of Locus is to represent structures using presheaves. It is important then
; that categories, which are one of the most basic and fundamental tools in presheaf theory,
; should be represented as presheaves. The topos of compositional quivers is our fundamental
; solution. In the broadest sense it consists of multisets of composition triples of a quiver.
; Categories are then just an important special case, used to form other topoi.

(deftype Compoid [quiver op]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this])

  StructuredQuiver
  (underlying-quiver [this] quiver)
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e]
    (transition quiver e)))

(derive Compoid :locus.set.logic.structure.protocols/copresheaf)

; Underlying relations and multirelations of compoids
(defmethod underlying-multirelation Compoid
  [^Compoid quiver] (underlying-multirelation (underlying-quiver quiver)))

(defmethod underlying-relation Compoid
  [^Compoid quiver] (underlying-relation (underlying-quiver quiver)))

(defmethod visualize Compoid
  [^Compoid quiver] (visualize (underlying-quiver quiver)))

; Get paths of a compositional structure
(defmethod paths Compoid
  [^Compoid quiver]

  (morphisms (.-op quiver)))

; Compositional ternary quivers
(defmulti compositional-ternary-quiver type)

(defmethod compositional-ternary-quiver Compoid
  [^Compoid quiver] (.-op quiver))

(defmethod to-ternary-quiver Compoid
  [^Compoid quiver] (compositional-ternary-quiver quiver))

; Get the successor quivers for a compositional structure
(defmethod successor-quiver Compoid
  [^Compoid compoid, cell-type]

  (cond
    (= cell-type '()) (identity-function (objects compoid))
    (= cell-type '(0)) (underlying-quiver compoid)
    (= cell-type '(0 0)) (compositional-ternary-quiver compoid)))

; Product and coproduct multimethods for the topos of compositional quivers
(defmethod product Compoid
  [& quivers]

  (->Compoid
    (apply quiver-product (map underlying-quiver quivers))
    (apply ternary-quiver-product (map compositional-ternary-quiver quivers))))

(defmethod coproduct Compoid
  [& quivers]

  (->Compoid
    (apply quiver-coproduct (map underlying-quiver quivers))
    (apply ternary-quiver-coproduct (map compositional-ternary-quiver quivers))))

; Multimethods to convert things into compositional quivers
(defmulti to-compoid type)

(defmethod to-compoid Compoid
  [^Compoid quiver] quiver)

; Subobjects in the topos of compositional quivers
(defn subcompoid
  [quiver new-paths new-morphisms new-objects]

  (->Compoid
    (subquiver (underlying-quiver quiver) new-morphisms new-objects)
    (ternary-subquiver (compositional-ternary-quiver quiver) new-paths new-morphisms)))

(defn restrict-quiver-composition
  [quiver new-paths]

  (->Compoid
    (underlying-quiver quiver)
    (wide-ternary-subquiver quiver new-paths)))

; Restrict the underlying quiver of a compositional quiver
(defn restrict-underlying-quiver
  [quiver new-morphisms new-objects]

  (->Compoid
    (subquiver (underlying-quiver quiver) new-morphisms new-objects)
    (full-ternary-subquiver (compositional-ternary-quiver quiver) new-morphisms)))

; Ontology of subobjects in the topos of compositional quivers
(defn subcompoid?
  [quiver new-paths new-morphisms new-objects]

  (and
    (subquiver? (underlying-quiver quiver) new-morphisms new-objects)
    (ternary-subquiver? (compositional-ternary-quiver quiver) new-paths new-morphisms)))

; Congruences in the topos of compositional quivers
(defn compoid-congruence?
  [quiver path-partition morphism-partition object-partition]

  (and
    (quiver-congruence? (underlying-quiver quiver) morphism-partition object-partition)
    (ternary-quiver-congruence? (compositional-ternary-quiver quiver) path-partition morphism-partition)))

(defn quotient-compositional-quiver
  [quiver path-partition morphism-partition object-partition]

  (->Compoid
    (quotient-quiver (underlying-quiver quiver) morphism-partition object-partition)
    (quotient-ternary-quiver (compositional-ternary-quiver quiver) path-partition morphism-partition)))

; Ontology of compositional quivers
(defn compoid?
  [quiver]

  (= (type quiver) Compoid))

(defn compositionally-thin-composition-quiver?
  [quiver]

  (and
    (compoid? quiver)
    (thin-ternary-quiver? (compositional-ternary-quiver quiver))))

(defn algebraic-compositional-quiver?
  [quiver]

  (and
    (compoid? quiver)
    (at-quiver? (compositional-ternary-quiver quiver))))
