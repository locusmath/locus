(ns locus.set.tree.two-quiver.path.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.tree.two-quiver.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all])
  (:import (locus.set.quiver.binary.core.object Quiver)))

; Path quivers are the basis of partial magmoids, magmoids, categories and a number of other
; related notions. They are a fundamental object in presheaf theoretic mathemtics, in particular,
; we see that every thin partial magmoid is completely determined by its underlying path quiver.
; Path quivers form their own topos.

(deftype PathQuiver [paths morphisms objects path-source path-target source target]
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  ConcreteObject
  (underlying-set [this]
    (->CartesianCoproduct [paths morphisms objects]))

  StructuredQuiver
  (underlying-quiver [this]
    (->Quiver
      morphisms
      objects
      source
      target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e]
    (list (source e) (target e)))

  StructuredTwoQuiver
  (two-morphisms [this] paths)
  (two-source-fn [this] path-source)
  (two-target-fn [this] path-target))

(derive PathQuiver :locus.set.tree.two-quiver.core.object/two-quiver)

(defmethod visualize PathQuiver
  [quiver] (visualize (underlying-quiver quiver)))

; Get the paths of a path quiver or other object of topos theory
(defmethod paths PathQuiver
  [^PathQuiver quiv]

  (.-paths quiv))

; Underlying multirelations for path quivers
(defmethod underlying-multirelation PathQuiver
  [quiver]

  (multiset
    (map
      (partial transition quiver)
      (morphisms quiver))))

(defmethod underlying-relation PathQuiver
  [quiver]

  (set (underlying-multirelation quiver)))

; We can get underlying path quivers for magmoids, partial magmoids, semigroupoids,
; categories, groupoids, and all other fundamental algebraic structures. In particular,
; when we define compositional quivers we will note how these compositional quivers
; can always be formed from adding extra structure to a path quiver.
(defmulti underlying-path-quiver type)

(defmethod underlying-path-quiver PathQuiver
  [^PathQuiver quiv] quiv)

(defmethod underlying-path-quiver :locus.set.copresheaf.structure.core.protocols/partial-magmoid
  [partial-magmoid]

  (->PathQuiver
    (paths partial-magmoid)
    (morphisms partial-magmoid)
    (objects partial-magmoid)
    first
    second
    (source-function partial-magmoid)
    (target-function partial-magmoid)))

; Full and empty path quivers provide us with a basic duality at the herat of partial
; magmoid theory and the theory of partial algebraic operations.
(defn full-path-quiver
  [quiver]

  (->PathQuiver
    (composability-relation quiver)
    (morphisms quiver)
    (objects quiver)
    first
    second
    (source-fn quiver)
    (target-fn quiver)))

(defn empty-path-quiver
  [quiver]

  (->PathQuiver
    #{}
    (morphisms quiver)
    (objects quiver)
    first
    second
    (source-fn quiver)
    (target-fn quiver)))

; Create a path quiver with a single object for use in the topos theory of partial algebra
(defn singular-path-quiver
  [path-quiver obj]

  (->PathQuiver
    (morphisms path-quiver)
    (objects path-quiver)
    #{obj}
    (source-fn path-quiver)
    (target-fn path-quiver)
    (constantly obj)
    (constantly obj)))

(defn singular-relational-path-quiver
  ([rel obj]
   (singular-relational-path-quiver (vertices rel) rel obj))
  ([vertices rel obj]
   (->PathQuiver
     rel
     vertices
     #{obj}
     first
     second
     (constantly obj)
     (constantly obj))))

; Conversion routines for creating path quivers
(defmulti to-path-quiver type)

(defmethod to-path-quiver PathQuiver
  [^PathQuiver quiver] quiver)

(defmethod to-path-quiver :default
  [obj] (underlying-path-quiver obj))

; Products and coproducts for path quivers
(defmethod product PathQuiver
  [& quivers]

  (->PathQuiver
    (apply cartesian-product (map paths quivers))
    (apply cartesian-product (map morphisms quivers))
    (apply cartesian-product (map objects quivers))
    (apply product (map s-function quivers))
    (apply product (map t-function quivers))
    (apply product (map source-function quivers))
    (apply product (map target-function quivers))))

(defmethod coproduct PathQuiver
  [& quivers]

  (->PathQuiver
    (apply cartesian-coproduct (map paths quivers))
    (apply cartesian-coproduct (map morphisms quivers))
    (apply cartesian-coproduct (map objects quivers))
    (apply coproduct (map s-function quivers))
    (apply coproduct (map t-function quivers))
    (apply coproduct (map source-function quivers))
    (apply coproduct (map target-function quivers))))

; Ontology of path quivers
(defn path-quiver?
  [quiv]

  (= (type quiv) PathQuiver))

(defn morphically-thin-path-quiver?
  [quiv]

  (and
    (path-quiver? quiv)
    (universal? (underlying-multirelation quiv))))

(defn path-thin-path-quiver?
  [quiv]

  (and
    (path-quiver? quiv)
    (universal? (underlying-two-multirelation quiv))))

(defn dually-thin-path-quiver?
  [quiv]

  (and
    (path-quiver? quiv)
    (universal? (underlying-multirelation quiv))
    (universal? (underlying-two-multirelation quiv))))
