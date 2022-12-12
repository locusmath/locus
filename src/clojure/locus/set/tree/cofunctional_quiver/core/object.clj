(ns locus.set.tree.cofunctional-quiver.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.tree.structure.core.protocols :refer :all]))

; A cofunctional quiver is a presheaf object of the topos Sets^C where C is the category consisting
; of three objects and seven morphisms: the identity morphisms, the source and target morphisms,
; a morphism exiting from the object set of the quiver, and two of its composites. As a copresheaf
; it is part of our ontology of copresheaves, and it can be understood in the context of a
; topos theoretic framework of presheaves.

(deftype CofunctionalQuiver [morphisms objects out op source target]
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this obj] (list (source obj) (target obj))))

(derive CofunctionalQuiver :locus.set.logic.structure.protocols/copresheaf)

; A basic constructor for cofunctional quivers
(defn cofunctional-quiver
  [func quiv]

  (->CofunctionalQuiver
    (morphisms quiv)
    (objects quiv)
    (outputs func)
    func
    (source-fn quiv)
    (target-fn quiv)))

; Constant objects in the topos of compositional quivers
(defn constant-cofunctional-quiver
  [coll]

  (cofunctional-quiver (identity-function coll) (constant-quiver coll)))

; Components of cofunctional quivers
(defn cofunctional-quiver-target
  [^CofunctionalQuiver quiver]

  (.-out quiver))

(defn function-of-cofunctional-quiver
   [^CofunctionalQuiver quiver]

  (->SetFunction
    (.-objects quiver)
    (.-out quiver)
    (.-op quiver)))

; Get the associated object partition of a cofunctional quiver
(defn associated-object-partition
  [^CofunctionalQuiver quiver]

  (let [func (function-of-cofunctional-quiver quiver)]
    (function-kernel func)))

; Successor quivers make cofunctional quivers into hierarchical cell complexes
(defmethod successor-quiver CofunctionalQuiver
  [^CofunctionalQuiver quiver, i]

  (case (count i)
    0 (identity-function (cofunctional-quiver-target quiver))
    1 (function-of-cofunctional-quiver quiver)
    2 (underlying-quiver quiver)))

; Conversion methods for cofunctional quivers
(defmulti to-cofunctional-quiver type)

(defmethod to-cofunctional-quiver CofunctionalQuiver
  [quiver] quiver)

; Relational components of cofunctional quivers
(defmethod underlying-multirelation CofunctionalQuiver
  [quiver] (multiset (underlying-multirelation (underlying-quiver quiver))))

(defmethod underlying-relation CofunctionalQuiver
  [quiver] (set (underlying-multirelation quiver)))

(defmethod visualize CofunctionalQuiver
  [quiver] (visualize (underlying-multirelation quiver)))

; Products and coproducts in the topos of compositional quivers
(defmethod product CofunctionalQuiver
  [& quivers]

  (->CofunctionalQuiver
    (apply product (map morphisms quivers))
    (apply product (map objects quivers))
    (apply product (map cofunctional-quiver-target quivers))
    (apply product (map function-of-cofunctional-quiver quivers))
    (apply product (map source-function quivers))
    (apply product (map target-function quivers))))

(defmethod coproduct CofunctionalQuiver
  [& quivers]

  (->CofunctionalQuiver
    (apply coproduct (map morphisms quivers))
    (apply coproduct (map objects quivers))
    (apply coproduct (map cofunctional-quiver-target quivers))
    (apply coproduct (map function-of-cofunctional-quiver quivers))
    (apply coproduct (map source-function quivers))
    (apply coproduct (map target-function quivers))))

; Ontology of cofunctional quivers
(defn cofunctional-quiver?
  [obj]

  (= (type obj) CofunctionalQuiver))