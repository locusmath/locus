(ns locus.set.quiver.relation.binary.mbr
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all])
  (:import [locus.set.logic.core.set Multiset]))

; As we extended our ontology to include support for multisets, we also need to extend our ontology
; of binary relations to provide better support for binary multirelations. These binary multirelations
; might emerge for example from the edge set of a quiver.

; A constructor for coreflexive multirelations
(defn coreflexive-multirelation
  [coll]

  (multiset (map (fn [i] (list i i)) coll)))

(defn symmetric-binary-multirelation
  [multifamily]

  (multiset
    (mapcat
     (fn [edge]
       (if (= (count edge) 1)
         (list (list (first edge) (first edge)))
         (let [ordered-edge (seq edge)]
           (list ordered-edge (reverse ordered-edge)))))
     multifamily)))

; Classes of binary multirelations
(defn binary-multirelation?
  [rel]

  (and
   (multiset? rel)
   (every? size-two-seq? rel)))

(def equal-binary-multirelation?
  (intersection
   equal-multiset?
   binary-multirelation?))

(defn coreflexive-multirelation?
  [rel]

  (and
    (multiset? rel)
    (coreflexive? (set rel))))

(defn irreflexive-multirelation?
  [rel]

  (and
    (multiset? rel)
    (irreflexive? (set rel))))

; A symmetric binary multirelation is multiplicity commutative
(defn symmetric-binary-multirelation?
  [rel]

  (let [supp (support rel)]
    (and
      (symmetric-binary-relation? supp)
      (every?
        (fn [i]
          (= (multiplicity rel i)
             (multiplicity rel (reverse i))))
        supp))))

; Classification of binary multirelations by their size
(def size-two-binary-multirelation?
  (intersection
    size-two-multiset?
    binary-multirelation?))

(def size-three-binary-multirelation?
  (intersection
    size-three-multiset?
    binary-multirelation?))

(def size-four-binary-multirelation?
  (intersection
    size-four-multiset?
    binary-multirelation?))





