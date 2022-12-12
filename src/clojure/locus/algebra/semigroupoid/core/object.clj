(ns locus.algebra.semigroupoid.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.algebra.category.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.algebra.semigroup.core.object Semigroup)
           (locus.algebra.category.core.object Category)
           (locus.order.lattice.core.object Lattice)
           (locus.set.quiver.binary.thin.object ThinQuiver)))

; A semigroupoid is a presheaf in the topos of compositional quivers. Its underlying quiver
; does not need to be a quiver with identity. It shares membership in this topos with
; magmoids and other related compositional structures. A semigroupoid has both a combinatorial
; structure consisting of a quiver and an algebraic structure consisting of a composition
; function. Semigroupoids are useful to us as generalisations of semigroups, which are
; necessary for example in the study of certain thin categories which form semilattices
; that don't have identity.
(deftype Semigroupoid [quiver op]
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

; Semigroupoid identification and testing which semigroupoids
; are actually valid categories
(derive Semigroupoid :locus.set.copresheaf.structure.core.protocols/semigroupoid)

; Special tests for categories as semigroupoids
(defn identity-morphism-element?
  [semigroupoid identity]

  (and
    (every?
      (fn [i]
        (and
          (or
            (not (composable-elements? semigroupoid identity i))
            (= (semigroupoid (list identity i)) i))
          (or
            (not (composable-elements? semigroupoid i identity))
            (= (semigroupoid (list i identity)) i))))
      (morphisms semigroupoid))))

(defn endomorphisms-map
  [quiver]

  (loop [coll (seq (morphisms quiver))
         rval {}]
    (if (empty? coll)
      rval
      (recur
        (rest coll)
        (let [current-morphism (first coll)]
          (if (= (source-element quiver current-morphism)
                 (target-element quiver current-morphism))
            (let [current-object (source-element quiver current-morphism)]
              (assoc
                rval
                current-object
                (conj (get rval current-object) current-morphism)))
            rval))))))

(defmethod category? Semigroupoid
  [semigroupoid]

  (let [objects (objects semigroupoid)
        endomorphisms (endomorphisms-map semigroupoid)]
    (every?
      (fn [obj]
        (let [current-endomorphisms (get endomorphisms obj)]
          (and
            (not (empty? current-endomorphisms))
            (not
              (every?
                (fn [i]
                  (not
                    (identity-morphism-element? semigroupoid i)))
                current-endomorphisms)))))
      objects)))

; Underlying relations
(defmethod underlying-relation Semigroupoid
  [semigroupoid] (underlying-relation (underlying-quiver semigroupoid)))

(defmethod underlying-multirelation Semigroup
  [semigroupoid] (underlying-multirelation (underlying-quiver semigroupoid)))

(defmethod visualize Semigroupoid
  [semigroupoid] (visualize (underlying-quiver semigroupoid)))

; Thin semigroupoids
(defn thin-semigroupoid
  ([rel]
   (thin-semigroupoid (vertices rel) rel))
  ([vertices edges]
   (->Semigroupoid
     (ThinQuiver. vertices edges)
     compose-ordered-pairs)))

; To semigroupoid
(defmulti to-semigroupoid type)

(defmethod to-semigroupoid Semigroupoid
  [obj] obj)

(defmethod to-semigroupoid Category
  [^Category category]

  (->Semigroupoid
    (.-quiver category)
    (.-op category)))

(defmethod to-semigroupoid Semigroup
  [semigroup]

  (->Semigroupoid
    (underlying-quiver semigroup)
    (.-op semigroup)))

(defmethod to-semigroupoid Lattice
  [lattice]

  (thin-semigroupoid (objects lattice) (morphisms lattice)))

(defmethod to-semigroupoid :locus.set.logic.core.set/universal
  [rel]

  (thin-semigroupoid rel))

; Strict total order semigroupoid
(defn strict-total-order-semigroupoid
  [n]

  (thin-semigroupoid
    (->SeqableRelation
      (->Upto n)
      (fn [[a b]]
        (< a b))
      {})))

; Adjoin a composition operation to a quiver
(defmethod adjoin-composition :locus.set.quiver.structure.core.protocols/quiver
  [quiv f]

  (->Semigroupoid quiv f))

; Products and coproducts in the category of semigroupoids
(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [& semigroupoids]

  (->Semigroupoid
    (apply coproduct (map underlying-quiver semigroupoids))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth semigroupoids i)]
          (list i (c (list v w))))))))

(defmethod product :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [& semigroupoids]

  (->Semigroupoid
    (apply product (map underlying-quiver semigroupoids))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        semigroupoids))))

(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/semigroup
  [& semigroups]

  (apply coproduct (map to-semigroupoid semigroups)))

; Duals of semigroupoids
(defmethod dual :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [semigroupoid]

  (->Semigroupoid (dual (underlying-quiver semigroupoid)) (comp semigroupoid reverse)))

; Get the endomorphism semigroup of an object of a semigroupoid
(defn endomorphism-semigroup
  [semigroupoid x]

  (->Semigroup
    (quiver-hom-class semigroupoid x x)
    semigroupoid))

; Subobjects of semigroupoids in the topos of composition quivers
(defn restrict-semigroupoid
  [semigroupoid new-morphisms new-objects]

  (->Semigroupoid
    (subquiver semigroupoid new-morphisms new-objects)
    (fn [[a b]]
      (semigroupoid (list a b)))))

(defn wide-subsemigroupoid
  [semigroupoid new-morphisms]

  (->Semigroupoid
    (wide-subquiver semigroupoid new-morphisms)
    (fn [[a b]]
      (semigroupoid (list a b)))))

(defn full-subsemigroupoid
  [semigroupoid new-objects]

  (->Semigroupoid
    (full-subquiver semigroupoid new-objects)
    (fn [[a b]]
      (semigroupoid (list a b)))))

; Ontology of subsemigroupoids
(defn subsemigroupoid?
  [semigroupoid new-morphisms new-objects]

  (and
    (subquiver? (underlying-quiver semigroupoid) new-morphisms new-objects)
    (compositionally-closed-set? semigroupoid new-morphisms)))

(defn enumerate-subsemigroupoids
  [semigroupoid]

  (filter
    (fn [[new-morphisms new-objects]]
      (compositionally-closed-set? semigroupoid new-morphisms))
    (subquivers (underlying-quiver semigroupoid))))

; Congruences of semigroupoids in the topos of composition quivers
(defn semigroupoid-congruence?
  [semigroupoid morphism-partition object-partition]

  (and
    (quiver-congruence? (underlying-quiver semigroupoid) morphism-partition object-partition)
    (compositional-congruence? semigroupoid morphism-partition)))

(defn semigroupoid-congruences
  [semigroupoid]

  (set
    (filter
      (fn [[morphism-partition object-partition]]
        (compositional-congruence? semigroupoid morphism-partition))
      (quiver-congruences (underlying-quiver semigroupoid)))))

; Special classes of semigroupoids
(defmethod thin-semigroupoid? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [semigroupoid]

  (thin-quiver? (underlying-quiver semigroupoid)))