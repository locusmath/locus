(ns locus.algebra.category.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.sequence.object :refer :all]
            [locus.set.quiver.relation.binary.product :refer :all]
            [locus.set.quiver.relation.binary.br :refer :all]
            [locus.set.quiver.relation.binary.sr :refer :all]
            [locus.set.quiver.relation.binary.vertices :refer :all]
            [locus.con.core.setpart :refer :all]
            [locus.set.mapping.general.core.object :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.set.copresheaf.structure.core.protocols :refer :all]
            [locus.order.general.core.object :refer :all]
            [locus.order.general.symmetric.object :refer :all]
            [locus.order.general.skeletal.object :refer :all]
            [locus.set.quiver.diset.core.object :refer :all]
            [locus.set.quiver.binary.core.object :refer :all]
            [locus.set.quiver.binary.thin.object :refer :all]
            [locus.set.copresheaf.quiver.unital.thin-object :refer :all]
            [locus.set.copresheaf.quiver.unital.object :refer :all]
            [locus.algebra.commutative.semigroup.object :refer :all]
            [locus.algebra.semigroup.core.object :refer :all]
            [locus.algebra.semigroup.monoid.object :refer :all]
            [locus.algebra.group.core.object :refer :all]
            [locus.order.lattice.core.object :refer :all]
            [locus.set.quiver.structure.core.protocols :refer :all])
  (:import (locus.order.lattice.core.object Lattice)
           (locus.set.copresheaf.quiver.unital.object UnitalQuiver)
           (locus.order.general.core.object Preposet)
           (locus.order.general.symmetric.object Setoid)
           (locus.order.general.skeletal.object Poset)
           (locus.algebra.group.core.object Group)))

; A category is a presheaf in the topos of compositional quivers. It shares membership in this
; topos with magmoids, semigroupoids, and other structures that have relaxed conditions. In
; addition to being presheaves themselves, categories are known as the organizing principle
; for presheaves and this makes them a distinctly important class of object.

; Categories can be defined by reference to two different components: their combinatorial
; structure and their algebraic structure. Their combinatorial structure can be defined
; by a unital quiver. Their algebraic structure can be defined as a ternary quiver
; and the properties if its composition operation can be studied with reference to the
; fundamental topos Sets^(->).

; While categories are defined as one type of presheaf structure, higher generalisations
; of categories are always defined over other types of presheaves. A two category, for example,
; has the combinatorial structure of a two globular set, which is an object understood
; by reference to the topos of two globular sets. Even higher categories are defined by other
; topoi of presheaves. As is befitting the Locus project's namesake, we always view
; everything from the lens of presheaf topos theory.

(deftype Category [quiver op]
  StructuredDiset
  (first-set [this] (first-set quiver))
  (second-set [this] (second-set quiver))

  StructuredQuiver
  (underlying-quiver [this] (underlying-quiver quiver))
  (source-fn [this] (source-fn quiver))
  (target-fn [this] (target-fn quiver))
  (transition [this e] (transition quiver e))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (identity-morphism-of quiver obj))
  (underlying-unital-quiver [this] quiver)

  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] (morphisms quiver))

  clojure.lang.IFn
  (invoke [this arg] (op arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Categories are semigroupoids with identity
(derive Category :locus.set.copresheaf.structure.core.protocols/category)

; Underlying relation
(defmethod underlying-multirelation :locus.set.copresheaf.structure.core.protocols/category
  [cat] (underlying-multirelation (underlying-unital-quiver cat)))

(defmethod underlying-relation :locus.set.copresheaf.structure.core.protocols/category
  [cat] (underlying-relation (underlying-unital-quiver cat)))

(defn underlying-preposet
  [cat] (Preposet. (second-set cat) (underlying-relation cat)))

(defmethod visualize :locus.set.copresheaf.structure.core.protocols/category
  [cat] (visualize (underlying-unital-quiver cat)))

(defmethod visualize :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [semigroupoid] (visualize (underlying-quiver semigroupoid)))

; Special support for thin categories
(defn compose-ordered-pairs
  [[[a b] [c d]]]

  (list c b))

(defn thin-category
  ([rel]
   (thin-category (vertices rel) rel))
  ([vertices edges]
   (->Category
     (thin-unital-quiver vertices edges)
     compose-ordered-pairs)))

; Create a discrete category
(defn discrete-category
  [coll]

  (thin-category coll (coreflexive-relation coll)))

; Convert various mathematical objects to categories
(defmulti to-category type)

(defmethod to-category Category
  [category] category)

(defmethod to-category :locus.set.copresheaf.structure.core.protocols/monoid
  [monoid]

  (->Category (underlying-unital-quiver monoid) monoid))

(defmethod to-category :locus.set.copresheaf.structure.core.protocols/semigroup
  [semigroup]

  (let [monoid (to-monoid (adjoin-identity semigroup))]
    (->Category
      (underlying-unital-quiver monoid)
      monoid)))

(defmethod to-category Group
  [group]

  (->Category (underlying-unital-quiver group) group))

(defmethod to-category Setoid
  [setoid]

  (thin-category (underlying-set setoid) (underlying-relation setoid)))

(defmethod to-category Poset
  [poset]

  (thin-category (underlying-set poset) (underlying-relation poset)))

(defmethod to-category Preposet
  [preposet]

  (thin-category (underlying-set preposet) (underlying-relation preposet)))

(defmethod to-category Lattice
  [lattice]

  (thin-category (second-set lattice) (first-set lattice)))

(defmethod to-category :locus.set.logic.core.set/universal
  [rel] (thin-category (set rel)))

; The topos of sets
(def sets
  (->Category
    (->UnitalQuiver
      set-function?
      universal?
      inputs
      outputs
      identity-function)
    (fn [[a b]]
      (compose a b))))

; Get the elements of a category as a structured set
(defn categorical-elements
  [category]

  (union
    (set
      (map
        (fn [arrow]
          (list 0 arrow))
        (morphisms category)))
    (set
      (map
        (fn [object]
          (list 1 object))
        (objects category)))))

; Get the quiver define over the generating set of morphisms of a category.
; In particular, this
(defn morphically-generated-subquiver
  [category]

  (->Quiver
    (morphic-gens category)
    (objects category)
    (source-fn category)
    (target-fn category)))

; Labeled thin categories allow us to better handle visualisation procedures:
; Vertices is a set of objects
; Edge map is a binary vector valued map
(defn simple-labeled-category
  [vertices edge-map]

  (let [edge-set (set (keys edge-map))
        flipped-map (into {} (map (fn [[k v]] [v k]) edge-map))]
    (Category.
      (UnitalQuiver.
        edge-set
        vertices
        (comp first edge-map)
        (comp second edge-map)
        (fn [obj]
          (flipped-map [obj obj])))
      (fn [[a b]]
        (let [[b1 b2] (edge-map a)
              [a1 a2] (edge-map b)]
          (flipped-map [a1 b2]))))))

; Adjoin composition to unital quivers
(defmethod adjoin-composition UnitalQuiver
  [quiv f]

  (Category. quiv f))

; Construct a category from a quiver directly
(defn extend-quiver
  [quiv comp id]

  (Category.
    (->UnitalQuiver
      (first-set quiv)
      (second-set quiv)
      (source-fn quiv)
      (target-fn quiv)
      id)
    comp))

; Inversions and isomorphism elements
(defn inverse-elements?
  [category a b]

  (and
    (bidirectionally-composable-elements? category a b)
    (identity-element? category (category (list a b)))
    (identity-element? category (category (list b a)))))

(defmethod inverse-elements :locus.set.copresheaf.structure.core.protocols/category
  [category a]

  (filter
    (fn [i]
      (inverse-elements? category a i))
    (morphisms category)))

(defn isomorphism-element?
  [category elem]

  (not
    (every?
      (fn [i]
        (not
          (inverse-elements? category elem i)))
      (morphisms category))))

(defn isomorphism-elements
  [category]

  (set
    (filter
      (fn [i]
        (isomorphism-element? category i))
      (morphisms category))))

; Products and coproducts in the category of categories
(defn category-product
  [& categories]

  (->Category
    (apply product (map underlying-unital-quiver categories))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        categories))))

(defn category-coproduct
  [& categories]

  (->Category
    (apply coproduct (map underlying-unital-quiver categories))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth categories i)]
          (list i (c (list v w))))))))

(defmethod product :locus.set.copresheaf.structure.core.protocols/category
  [& categories] (apply category-product categories))

(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/category
  [& categories] (apply category-coproduct categories))

; The coproduct of monoids
; The coproduct of monoids can be computed by converting each of the individual
; monoids into categories and computing the coproduct from that.
(defmethod coproduct :locus.set.copresheaf.structure.core.protocols/monoid
  [& monoids]

  (apply coproduct (map to-category monoids)))

(defmethod dual :locus.set.copresheaf.structure.core.protocols/category
  [cat]

  (Category.
    (dual (underlying-unital-quiver cat))
    (comp cat reverse)))

; Get the endomorphism monoid of an object of a category
(defn endomorphism-monoid
  [category x]

  (->Monoid
    (quiver-hom-class category x x)
    category
    (identity-morphism-of category x)))

; We need some way of dealing with subobjects of categories
(defn restrict-category
  [category new-morphisms new-objects]

  (->Category
    (unital-subquiver (underlying-unital-quiver category) new-morphisms new-objects)
    category))

(defn wide-subcategory
  [category new-morphisms]

  (->Category
    (wide-unital-subquiver (underlying-unital-quiver category) new-morphisms)
    category))

(defn full-subcategory
  [category new-objects]

  (->Category
    (full-unital-subquiver (underlying-unital-quiver category) new-objects)
    category))

; Testing for subcategories
(defn compositionally-closed-set?
  [category coll]

  (every?
    (fn [[a b]]
      (or
        (not (composable-elements? category a b))
        (contains? coll (category (list a b)))))
    (cartesian-power coll 2)))

(defn subcategory?
  [category new-morphisms new-objects]

  (let [quiv (underlying-unital-quiver category)]
    (and
      (unital-subquiver? quiv new-morphisms new-objects)
      (compositionally-closed-set? category new-morphisms))))

(defn enumerate-subcategories
  [category]

  (filter
    (fn [[morphism-set object-set]]
      (compositionally-closed-set? category morphism-set))
    (unital-subquivers (underlying-unital-quiver category))))

; Composition closure of subcategories
(defn morphism-objects-set
  ([morphism]
   (set (list (source-object morphism) (target-object morphism))))
  ([category morphism]
   (set
     (list
       (source-element category morphism)
       (target-element category morphism)))))

(defn composition-closure
  [category coll]

  (let [new-composites (set
                         (for [[a b] (cartesian-power coll 2)
                               :when (composable-elements? category a b)]
                           (category (list a b))))]
    (if (superset? (list new-composites coll))
      coll
      (composition-closure category (union coll new-composites)))))

(defn subcategory-closure
  [category [new-morphisms new-objects]]

  (let [induced-objects (apply
                          union
                          (map
                            (partial morphism-objects-set category)
                            new-morphisms))
        all-objects (union new-objects induced-objects)
        identities (identity-morphisms-of category all-objects)
        composite-morphisms (composition-closure category new-morphisms)
        all-morphisms (union new-morphisms composite-morphisms identities)]
    [all-morphisms all-objects]))

(defmethod sub :locus.set.copresheaf.structure.core.protocols/category
  [category]

  (Lattice.
    (->SeqableUniversal
      (fn [[a b]]
        (subcategory? category a b))
      (enumerate-subcategories category)
      {})
    (comp
      (partial subcategory-closure category)
      join-set-pairs)
    meet-set-pairs))

; Categorical congruences
(defn compositional-congruence?
  [category partition]

  (let [current-map (partition->projection partition)
        composability-partition (pn
                                  (fn [[a b] [c d]]
                                    (and
                                      (= (current-map a) (current-map c))
                                      (= (current-map b) (current-map d))))
                                  (composability-relation category))]
    (every?
      (fn [equal-composites]
        (equal-seq?
          (map
            (fn [pair]
              (let [current-composite (category pair)]
                (current-map current-composite)))
            equal-composites)))
      composability-partition)))

(defn compositional-congruences
  [category]

  (filter
    (fn [morphism-partition]
      (compositional-congruence? category morphism-partition))
    (enumerate-set-partitions (morphisms category))))

(defn categorical-congruence?
  [category morphism-partition object-partition]

  (let [quiver (underlying-unital-quiver category)]
    (and
     (unital-quiver-congruence? quiver morphism-partition object-partition)
     (compositional-congruence? category morphism-partition))))

(defn ^{:private true} fixed*
  [pair-partitions]

  (set
    (map
      (fn [[a b]]
        (list
          (set (map set a))
          (set (map set b))))
      pair-partitions)))

(defn categorical-congruences
  [category]

  (filter
    (fn [[morphism-partition object-partition]]
      (compositional-congruence? category morphism-partition))
    (fixed* (unital-quiver-congruences (underlying-unital-quiver category)))))

(defn categorical-congruences-relation
  [category]

  (set
    (filter
      (fn [[a b]]
        (= a (meet-set-pair-congruences a b)))
      (cartesian-power (set (categorical-congruences category)) 2))))

; We need a special piece of functionality for dealing with numeric quivers
(defn numeric-quiver
  [n coll]

  (->Quiver
    (->RangeSet 0 (count coll))
    (->RangeSet 0 n)
    (fn [i]
      (first (nth coll i)))
    (fn [j]
      (second (nth coll j)))))

; Fundamental types of categories
(defn nth-discrete-category
  [n]

  (extend-quiver
    (numeric-quiver
      n
      (map (fn [i] (list i i)) (range n)))
    (fn [[a b]] b)
    identity))

(defn nth-complete-thin-groupoid
  [n]

  (thin-category
    (complete-relation (set (range n)))))

; Functional logic index categories
; An n pair category is the coproduct of ordered pair categories
(defn n-pair-category
  [n]

  (thin-category
    (->RangeSet 0 (* 2 n))
    (union
      (set
        (map
          (fn [i]
            (list i i))
          (range (* 2 n))))
      (set
        (map
          (fn [i]
            (list (* 2 i) (inc (* 2 i))))
          (range n))))))

; Get an unordered n pair category
; An undordered n pair category is the coproduct of unordered pair categories
(defn unordered-n-pair-category
  [n]

  (thin-category
    (->RangeSet 0 (* 2 n))
    (apply
      union
      (map
        (fn [i]
          #{(list i i)
            (list (inc i) (inc i))
            (list i (inc i))
            (list (inc i) i)})
        (range 0 (* 2 n) 2)))))

; Higher diamond categories
; Higher diamond categories are height three lattices described as categories
; Every height three lattice is a weak order with no more than one upper bound
; and no more then one lower bound, so they are always fully determined
; by their object count.
(defn nth-higher-diamond-category
  [n]

  (thin-category
    (weak-order
      [#{0}
       (set (range 1 (inc n)))
       #{(inc n)}])))

; N arrow categories
; If we are to combine N different arrows in a category, then they can either be
; parallel, have common inputs, have common outputs, or be disjoint.
(defn n-arrow-category
  [n]

  (extend-quiver
    (numeric-quiver
      2
      (concat
        (list (list 0 0) (list 1 1))
        (repeat n (list 0 1))))
    (fn [[a b]]
      (cond
        (<= a 1) b
        (<= b 1) a
        :else nil))
    identity))

; Span and cospan categories for topos of copresheaves
(defn n-cospan-category
  [n]

  (thin-category
    (->RangeSet 0 (inc n))
    (union
      (set
        (map
          (fn [i]
            (list i i))
          (range (inc n))))
      (set
        (map
          (fn [i]
            (list i 0))
          (range 1 (inc n)))))))

(defn n-span-category
  [n]

  (thin-category
    (->RangeSet 0 (inc n))
    (union
      (set
        (map
          (fn [i]
            (list i i))
          (range (inc n))))
      (set
        (map
          (fn [i]
            (list 0 i))
          (range 1 (inc n)))))))

; Index categories for chain copresheaves
(defn nth-total-order-category
  [n]

  (let [coll (range (inc n))
        rel (apply total-order coll)]
    (thin-category
      (set coll)
      rel)))

; The construction of a free category from a quiver
(defn free-category
  [quiver]

  (extend-quiver
    (->Quiver
      (fn [[start end path]]
        (and
          (composition-path? quiver path)
          (or
            (empty? path)
            (and
              (= (source-element quiver (last path)) start)
              (= (target-element quiver (first path)) end)))))
      (objects quiver)
      first
      second)
    (fn [[[start1 end1 path1] [start2 end2 path2]]]
      [start2 end1 (into path1 path2)])
    (fn [obj]
      [obj obj []])))

; Special classes of categories
(defn connected-category?
  [category]

  (and
    (category? category)
    (<= (count (weak-connectivity (underlying-relation category))) 1)))

(defn skeletal-category?
  [category]

  (and
    (category? category)
    (every?
      (fn [morphism]
        (or
          (identity-element? category morphism)
          (not (isomorphism-element? category morphism))))
      (morphisms category))))

(defn two-object-category?
  [category]

  (and
    (category? category)
    (= (count (objects category)) 2)))

(defn three-object-category?
  [category]

  (and
    (category? category)
    (= (count (objects category)) 3)))

(defn four-object-category?
  [category]

  (and
    (category? category)
    (= (count (objects category)) 4)))

; Our ontology of categories is divided into the double-arrow free categories, for which given any
; distinct A,B them Hom(A,B) has no more than one member and everything else. The double arrow free
; categories include the most basic forms of categories: preorders and monoids. So they are the
; simplest categories that we can start with.
(defn double-arrow-free-category?
  [category]

  (and
    (category? category)
    (loop [remaining-morphisms (seq (morphisms category))
           found-pairs #{}]
      (if (empty? remaining-morphisms)
        true
        (let [current-morphism (first remaining-morphisms)
              [a b] (transition category current-morphism)]
          (if (= a b)
            (recur
              (rest remaining-morphisms)
              found-pairs)
            (if (contains? found-pairs [a b])
              false
              (recur
                (rest remaining-morphisms)
                (conj found-pairs [a b])))))))))

; Ontology of thin categories
(defmethod thin-category? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [x]

  (and
    (category? x)
    (thin-quiver? (underlying-quiver x))))

(defn connected-thin-category?
  [category]

  (and
    (thin-category? category)
    (<= (count (weak-connectivity (underlying-relation category))) 1)))

; Ontology of thin groupoids
(defmethod thin-groupoid? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [x]

  (and
    (category? x)
    (symmetric-thin-quiver? (underlying-quiver x))))

(defn complete-thin-groupoid?
  [category]

  (and
    (category? category)
    (complete-thin-quiver? (underlying-quiver category))))

(defn discrete-category?
  [category]

  (and
    (category? category)
    (coreflexive-thin-quiver? (underlying-quiver category))))

(defn regular-thin-groupoid?
  [category]

  (and
    (thin-category? category)
    (regular-equivalence-relation? (underlying-relation category))))

(defn two-regular-thin-groupoid?
  [category]

  (and
    (thin-category? category)
    (two-regular-equivalence-relation? (underlying-relation category))))

(defn three-regular-thin-groupoid?
  [category]

  (and
    (thin-category? category)
    (three-regular-equivalence-relation? (underlying-relation category))))

(defn four-regular-thin-groupoid?
  [category]

  (and
    (thin-category? category)
    (four-regular-equivalence-relation? (underlying-relation category))))

; Total preorders
(defn total-order-category?
  [category]

  (and
    (thin-category? category)
    (total-order? (underlying-relation category))))

(defn total-preorder-category?
  [category]

  (and
    (thin-category? category)
    (total-preorder? (underlying-relation category))))

; Gem categories
(defn gem-relation?
  [rel]

  (and
    (total-preorder? rel)
    (every?
      (fn [i]
        (= (count i) 2))
      (strong-connectivity rel))))

(defn gem-category?
  [category]

  (and
    (= (count (objects category)) 4)
    (thin-category? category)
    (let [rel (underlying-relation category)]
      (gem-relation? rel))))

; Endotrivial categories constructed by coproducts
(defn n-pair-category?
  [category]

  (and
    (thin-category? category)
    (set-of-ordered-pairs? (underlying-relation category))))

(defn n-gem-category?
  [category]

  (and
    (thin-category? category)
    (let [rel (underlying-relation category)]
      (every?
        (fn [component]
          (gem-relation? component))
        (weakly-connected-components rel)))))

; Additional classes of categories constructed by weak orders
(defn n-span-category?
  [category]

  (and
    (thin-category? category)
    (height-two-lower-tree? (underlying-relation category))))

(defn n-cospan-category?
  [category]

  (and
    (thin-category? category)
    (height-two-upper-tree? (underlying-relation category))))

; Diamond categories
(defn diamond-relation?
  [rel]

  (and
    (weak-order? rel)
    (= [1 2 1] (vec (map count (lower-first-ranking rel))))))

(defn double-diamond-relation?
  [rel]

  (and
    (weak-preorder? rel)
    (let [components (strong-connectivity rel)]
      (and
        (every?
          (fn [i]
            (= (count i) 2))
          components)
        (let [component-selections (map first components)
              selected-relation (subrelation rel component-selections)]
          (diamond-relation? selected-relation))))))

(defn double-diamond-category?
  [category]

  (and
    (thin-category? category)
    (= (count (objects category)) 8)
    (double-diamond-relation? (underlying-relation category))))

(defn diamond-category?
  [category]

  (and
    (thin-category? category)
    (= (count (objects category)) 4)
    (diamond-relation? (underlying-relation category))))

(defn higher-diamond-category?
  [category]

  (and
    (thin-category? category)
    (let [rel (underlying-relation category)]
      (and
        (weak-order? rel)
        (let [ranking (lower-first-ranking rel)]
          (and
            (= (count ranking) 3)
            (= (count (first ranking)) 1)
            (= (count (last ranking)) 1)))))))

; Collections of diamond copresheaves
(defn n-diamond-category?
  [category]

  (and
    (thin-category? category)
    (let [rel (underlying-relation category)]
      (every?
        (fn [component]
          (diamond-relation? component))
        (weakly-connected-components rel)))))

; Cubes are the product of the ordered pair with diamonds
(defn cube-category?
  [category]

  (and
    (thin-category? category)
    (= (count (objects category)) 8)
    (boolean-algebra-relation? (underlying-relation category))))

; A general theory of skeletal thin categories
(defn skeletal-thin-category?
  [category]

  (and
    (category? category)
    (posetal-quiver? (underlying-quiver category))))

(defmethod lattice? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [x]

  (and
    (thin-category? x)
    (lattice-relation? (underlying-relation x))))

; Endomorphism only categories
(defmethod monoid? :locus.set.copresheaf.structure.core.protocols/monoid
  [x]

  (= (count (objects x)) 1))

(defn coproduct-of-monoids?
  [category]

  (and
    (category? category)
    (coreflexive? (underlying-relation category))))

(defn coproduct-of-groups?
  [category]

  (and
    (groupoid? category)
    (coproduct-of-monoids? category)))

; Endotrivial categories
(defn endotrivial-category?
  [category]

  (and
    (category? category)
    (loop [remaining-morphisms (seq (morphisms category))
           found-objects #{}]
      (if (empty? remaining-morphisms)
        true
        (let [current-morphism (first remaining-morphisms)
              [a b] (transition category current-morphism)]
          (if (not= a b)
            (recur
              (rest remaining-morphisms)
              found-objects)
            (if (contains? found-objects a)
              false
              (recur
                (rest remaining-morphisms)
                (conj found-objects a)))))))))

(defn connected-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (<= (count (weak-connectivity (underlying-relation category))) 1)))

; Ontology of totally preordered categories without non-trivial endomorphisms
(defn totally-preordered-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (total-preorder? (underlying-relation category))))

(defn totally-ordered-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (total-order? (underlying-relation category))))

(defn ordered-pair-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (= (count (objects category)) 2)
    (total-order? (underlying-relation category))))

(defn ordered-triple-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (= (count (objects category)) 3)
    (total-order? (underlying-relation category))))

(defn ordered-quadruple-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (= (count (objects category)) 4)
    (total-order? (underlying-relation category))))

(defn n-arrow-category?
  [category]

  (and
    ; check that the argument structure is indeed a category
    (category? category)

    ; every n arrow category has at most two objects
    (= (count (objects category)) 2)

    ; check that it also has a total order underneath it
    (or
      (discrete-category? category)
      (total-order? (underlying-relation category)))

    ; check that all endomorphism monoids are trivial
    (endotrivial-category? category)))

(defn one-arrow-category?
  [category]

  (and
    (n-arrow-category? category)
    (= (count (morphisms category)) 3)))

(defn two-arrow-category?
  [category]

  (and
    (n-arrow-category? category)
    (= (count (morphisms category)) 4)))

(defn three-arrow-category?
  [category]

  (and
    (n-arrow-category? category)
    (= (count (morphisms category)) 5)))

(defn four-arrow-category?
  [category]

  (and
    (n-arrow-category? category)
    (= (count (morphisms category)) 6)))

; Skeletal endotrivial categories
(defn skeletal-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (antisymmetric? (underlying-relation category))))

; Special classes of categories
(defmethod groupoid? :locus.set.copresheaf.structure.core.protocols/semigroupoid
  [category]

  (or
    (isa? (type category) :locus.set.copresheaf.structure.core.protocols/groupoid)
    (and
      (category? category)
      (every?
        (fn [morphism]
          (isomorphism-element? category morphism))
        (morphisms category)))))

(defn permutable-quiver-index-category?
  [category]

  (and
    (category? category)
    (= (count (objects category)) 2)
    (let [rel (underlying-relation category)]
      (and
        (total-order? rel)
        (let [a (first (minimal-vertices rel))
              b (first (maximal-vertices rel))]
          (= 2 (quiver-hom-cardinality category a b))
          (= 2 (quiver-hom-cardinality category a a))
          (let [[source target] (seq (quiver-hom-class category a b))
                edge-identity (identity-morphism-of category a)
                transpose (first
                            (disj
                              (set
                                (quiver-hom-class category a a))
                              edge-identity))]
            (and
              (= (category (list transpose transpose)) edge-identity)
              (= (category (list source transpose)) target)
              (= (category (list target transpose)) source))))))))