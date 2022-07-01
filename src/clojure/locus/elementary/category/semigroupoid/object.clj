(ns locus.elementary.category.semigroupoid.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.category.core.object :refer :all])
  (:import (locus.elementary.semigroup.core.object Semigroup)
           (locus.elementary.category.core.object Category)
           (locus.elementary.lattice.core.object Lattice)))

; A semigroupoid is an object of the topos Quiv x Sets^(->) consisting of the data
; a quiver and a composition function on it. Thusly, there are two copresheaf
; valued functors on the category of semigroupoids that define it. We work with
; semigroupoids in order to define a generalisation of categories that includes
; semigroups. We need semigroups in turn, for example when considering semilattices
; of thin categories that don't have identities.
(deftype Semigroupoid [morphisms objects source target func]
  ; Semigroupoids are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  ; Semigroupoids are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Semigroupoid identification and testing which semigroupoids
; are actually valid categories
(derive Semigroupoid :locus.elementary.function.core.protocols/semigroupoid)

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

; Special classes of semigroupoids
(defn thin-semigroupoid?
  [semigroupoid]

  (and
    (semigroupoid? semigroupoid)
    (thin-quiver? (underlying-quiver semigroupoid))))

; Underlying relations
(defmethod underlying-relation Semigroupoid
  [semigroupoid] (underlying-relation (underlying-quiver semigroupoid)))

; To semigroupoid
(defmulti to-semigroupoid type)

(defmethod to-semigroupoid Semigroupoid
  [obj] obj)

(defmethod to-semigroupoid Semigroup
  [semigroup]

  (Semigroupoid.
    (underlying-set semigroup)
    #{0}
    (constantly 0)
    (constantly 0)
    (.op semigroup)))

(defmethod to-semigroupoid Category
  [category]

  (Semigroupoid.
    (morphisms category)
    (objects category)
    (source-fn category)
    (target-fn category)
    (.func category)))

; Thin semigroupoids
(defn thin-semigroupoid
  ([rel] (thin-semigroupoid (vertices rel) rel))
  ([vertices edges]
   (Semigroupoid.
     edges
     vertices
     first
     second
     compose-ordered-pairs)))

(defmethod to-semigroupoid Lattice
  [lattice]

  (thin-semigroupoid (second-set lattice) (first-set lattice)))

; Strict total order semigroupoid
(defn strict-total-order-semigroupoid
  [n]

  (thin-semigroupoid
    (->SeqableRelation
      (seqable-interval 0 n)
      (fn [[a b]]
        (< a b))
      {})))

; Adjoin a composition operation to a quiver
(defmethod adjoin-composition :locus.elementary.quiver.core.object/quiver
  [quiv f]

  (->Semigroupoid
    (morphisms quiv)
    (objects quiv)
    (source-fn quiv)
    (target-fn quiv)
    f))

; Coproduct of semigroupoids
(defmethod coproduct :locus.elementary.function.core.protocols/semigroupoid
  [& semigroupoids]

  (Semigroupoid.
    (apply cartesian-coproduct (map first-set semigroupoids))
    (apply cartesian-coproduct (map second-set semigroupoids))
    (fn [[i v]]
      (let [current-semigroupoid (nth semigroupoids i)]
        (list i ((source-fn current-semigroupoid) v))))
    (fn [[i v]]
      (let [current-semigroupoid (nth semigroupoids i)]
        (list i ((target-fn current-semigroupoid) v))))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth semigroupoids i)]
          (list i (c (list v w))))))))

(defmethod product :locus.elementary.function.core.protocols/semigroupoid
  [& semigroupoids]

  (Semigroupoid.
    (apply cartesian-product (map first-set semigroupoids))
    (apply cartesian-product (map second-set semigroupoids))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          (let [current-semigroupoid (nth semigroupoids i)]
            ((source-fn current-semigroupoid) v)))
        morphisms))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          (let [current-semigroupoid (nth semigroupoids i)]
            ((target-fn current-semigroupoid) v)))
        morphisms))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        semigroupoids))))

; The coproducts of semigroups
(defmethod coproduct :locus.elementary.function.core.protocols/semigroup
  [& semigroups]

  (apply coproduct (map to-semigroupoid semigroups)))

(defmethod dual :locus.elementary.function.core.protocols/semigroupoid
  [semigroupoid]

  (Semigroupoid.
    (first-set semigroupoid)
    (second-set semigroupoid)
    (.target semigroupoid)
    (.source semigroupoid)
    (comp semigroupoid reverse)))


