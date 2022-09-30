(ns locus.elementary.category.core.object
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.sequence.core.object :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.vertices :refer :all]
            [locus.base.partition.core.setpart :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.elementary.copresheaf.core.protocols :refer :all]
            [locus.elementary.category.relation.set-relation :refer :all]
            [locus.elementary.order.core.object :refer :all]
            [locus.elementary.preorder.core.object :refer :all]
            [locus.elementary.preorder.setoid.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.quiver.core.thin-object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.semigroup.monoid.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all])
  (:import (locus.elementary.lattice.core.object Lattice)
           (locus.elementary.semigroup.monoid.object Monoid)
           (locus.elementary.quiver.unital.object UnitalQuiver)
           (locus.elementary.preorder.core.object Preposet)
           (locus.elementary.preorder.setoid.object Setoid)
           (locus.elementary.order.core.object Poset)))

; In topos theoretic foundations, we typically focus on copresheaves over categories.
; At first we can build up our copresheaves over a limited set of index categories,
; such as preorders containing only a couple of elements, but eventually we need
; to provide a general framework for handling arbitrary categories. Once we have that
; framework then we can deal with arbitrary copresheaves.

; Nonetheless, we can interpret a category by a number of copresheaves defined over it,
; so that categories fit into our system of topos theoretic foundations. The first is
; the topos of quivers. Every category is associated with an underlying quiver,
; which leads to the functor f : Cat -> Quiv by which we can better interpret categories
; by one of the foundational copresheaves.

; Secondly, there are forgetful set-valued functors which filter through Quiv to
; Sets^2 and from there to Sets. The functor to Sets^2 maps a category to a pair
; consisting of its morphism set and its object set. The last aspect of the topos theoretic
; foundation of categories is the functor to Sets^(->). The composition function of a
; category leads to a functor f: Cats -> Sets^(->). Together the data of these copresheaves
; make up a category, which itself can be understood in terms of copresheaves in
; our system of topos theoretic foundations.

(deftype Category [morphisms objects source target func id]
  ; Categories are structured quivers
  StructuredDiset
  (first-set [this] morphisms)
  (second-set [this] objects)

  StructuredQuiver
  (underlying-quiver [this] (->Quiver morphisms objects source target))
  (source-fn [this] source)
  (target-fn [this] target)
  (transition [this e] (list (source e) (target e)))

  StructuredUnitalQuiver
  (identity-morphism-of [this obj] (id obj))
  (underlying-unital-quiver [this] (->UnitalQuiver morphisms objects source target id))

  ; Categories are structured functions
  ConcreteMorphism
  (inputs [this] (composability-relation this))
  (outputs [this] morphisms)

  clojure.lang.IFn
  (invoke [this arg] (func arg))
  (applyTo [this args] (clojure.lang.AFn/applyToHelper this args)))

; Categories are semigroupoids with identity
(derive Category :locus.elementary.copresheaf.core.protocols/category)

; Compose ordered pairs
(defn compose-ordered-pairs
  [[[a b] [c d]]]

  (list c b))

; Get the quiver define over the generating set of morphisms of a category.
; In particular, this
(defn morphically-generated-subquiver
  [category]

  (->Quiver
    (morphic-gens category)
    (objects category)
    (source-fn category)
    (target-fn category)))

; We need some way of testing for identity morphisms
(defn identity-element?
  [category identity]

  (let [source (source-element category identity)
        target (target-element category identity)]
    (and
      (= source target)
      (= ((.id category) source) identity))))

(defn inverse-elements?
  [category a b]

  (and
    (bidirectionally-composable-elements? category a b)
    (identity-element? category (category (list a b)))
    (identity-element? category (category (list b a)))))

(defn inverse-elements
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

; Underlying relation
(defmethod underlying-relation :locus.elementary.copresheaf.core.protocols/category
  [cat] (underlying-relation (underlying-quiver cat)))

; General conversion methods
(defmulti to-category type)

(defmethod to-category Category
  [cat] cat)

; Conversion of monoids
(defmethod to-category :locus.elementary.copresheaf.core.protocols/monoid
  [mon]

  (Category.
    (morphisms mon)
    (objects mon)
    (source-fn mon)
    (target-fn mon)
    mon
    (fn [x]
      (when (zero? x)
        (.id mon)))))

(defmethod to-category :locus.elementary.copresheaf.core.protocols/group
  [group]

  (to-category
    (Monoid.
      (.elems group)
      (.op group)
      (.id group))))

; Thin categories
; These are constructed without the context of edge labelings so they might
; not produce as nice of diagrams for the copresheaf viewer.
(defn thin-category
  ([rel] (thin-category (vertices rel) rel))
  ([vertices edges]
   (Category.
     edges
     vertices
     first
     second
     compose-ordered-pairs
     (fn [x] (list x x)))))

; Labeled thin categories allow us to better handle visualisation procedures
; Vertices is a set of objects
; Edge map is a binary vector valued map
(defn simple-labeled-category
  [vertices edge-map]

  (let [edge-set (set (keys edge-map))
        flipped-map (into {} (map (fn [[k v]] [v k]) edge-map))]
    (Category.
      edge-set
      vertices
      (comp first edge-map)
      (comp second edge-map)
      (fn [[a b]]
        (let [[b1 b2] (edge-map a)
              [a1 a2] (edge-map b)]
          (flipped-map [b1 a2])))
      (fn [obj]
        (flipped-map [obj obj])))))

; Conversion of thin categories
(defn underlying-preposet
  [cat]

  (Preposet. (second-set cat) (underlying-relation cat)))

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

; The topos of sets
(def sets
  (Category.
    set-function?
    universal?
    inputs
    outputs
    (fn [[a b]]
      (compose a b))
    identity-function))

; We now need some way of getting the products and coproducts of categories
(defmethod product :locus.elementary.copresheaf.core.protocols/category
  [& categories]

  (Category.
    (apply cartesian-product (map first-set categories))
    (apply cartesian-product (map second-set categories))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          ((source-fn (nth categories i)) v))
        morphisms))
    (fn [morphisms]
      (map-indexed
        (fn [i v]
          ((target-fn (nth categories i)) v))
        morphisms))
    (fn [[morphisms1 morphisms2]]
      (map-indexed
        (fn [i c]
          (c (list (nth morphisms1 i) (nth morphisms2 i))))
        categories))
    (fn [obj]
      (map-indexed
        (fn [i v]
          ((.id ^Category (nth categories i)) v))
        obj))))

(defmethod coproduct :locus.elementary.copresheaf.core.protocols/category
  [& categories]

  (Category.
    (apply cartesian-coproduct (map first-set categories))
    (apply cartesian-coproduct (map second-set categories))
    (fn [[i v]]
      (list i ((source-fn (nth categories i)) v)))
    (fn [[i v]]
      (list i ((target-fn (nth categories i)) v)))
    (fn [[[i v] [j w]]]
      (when (= i j)
        (let [c (nth categories i)]
          (list i (c (list v w))))))
    (fn [[i v]]
      (list i ((.id ^Category (nth categories i)) v)))))

(defmethod dual :locus.elementary.copresheaf.core.protocols/category
  [cat]

  (Category.
    (first-set cat)
    (second-set cat)
    (.target cat)
    (.source cat)
    (comp cat reverse)
    (.id cat)))

; The coproduct of monoids
; The coproduct of monoids can be computed by converting each of the individual
; monoids into categories and computing the coproduct from that.
(defmethod coproduct :locus.elementary.copresheaf.core.protocols/monoid
  [& monoids]

  (apply coproduct (map to-category monoids)))

; We need some way of dealing with subcategories
(defn restrict-category
  [category new-morphisms new-objects]

  (Category.
    new-morphisms
    new-objects
    (.source category)
    (.target category)
    (.func category)
    (.id category)))

; We now need some way of getting wide and full subcategories
(defn enumerate-full-subcategory-morphisms
  [category new-objects]

  (set
    (filter
      (fn [i]
        (let [source ((.source category) i)
              target ((.target category) i)]
          (and
            (contains? new-objects source)
            (contains? new-objects target))))
      (first-set category))))

(defn wide-subcategory
  [category new-morphisms]

  (restrict-category
    category
    new-morphisms
    (second-set category)))

(defn full-subcategory
  [category new-objects]

  (restrict-category
    category
    (enumerate-full-subcategory-morphisms category new-objects)
    new-objects))

; The morphism objects set has to be adapted to deal either with elements
; of a morphism class or morphic elements of category.
(defn morphism-objects-set
  ([morphism]
   (set (list (source-object morphism) (target-object morphism))))
  ([category morphism]
   (set
     (list
       ((.source category) morphism)
       ((.target category) morphism)))))

; Composition closure
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
        identities (set (map (.id category) all-objects))
        composite-morphisms (composition-closure category new-morphisms)
        all-morphisms (union new-morphisms composite-morphisms identities)]
    [all-morphisms all-objects]))

(defn subcategory?
  [category new-morphisms new-objects]

  (let [[all-morphisms all-objects] (subcategory-closure
                                      category
                                      [new-morphisms new-objects])]
    (and
      (= new-morphisms all-morphisms)
      (= new-objects all-objects))))

(defn enumerate-subcategories
  [category]

  (filter
    (fn [[morphisms objects]]
      (subcategory? category morphisms objects))
    (seqable-cartesian-product
      (seqable-power-set (.morphisms category))
      (seqable-power-set (.objects category)))))

(defmethod sub :locus.elementary.copresheaf.core.protocols/category
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

; Adjoin composition to unital quivers
(defmethod adjoin-composition UnitalQuiver
  [quiv f]

  (Category.
    (first-set quiv)
    (second-set quiv)
    (source-fn quiv)
    (target-fn quiv)
    f
    (.id quiv)))

; Construct a category from a quiver directly
(defn extend-quiver
  [quiv comp id]

  (Category.
    (first-set quiv)
    (second-set quiv)
    (source-fn quiv)
    (target-fn quiv)
    comp
    id))

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

; The new theory of doubles of categories
; A double of a category C combines it in an ordered fashion with
; itself C+C, so it has twice as many objects as its predecessor.
; On the other hand, it has three times as many morphisms, defined
; by freely combining morphisms from one category to the other
; in an ordered fashion.
(defn double-category
  [category]

  (Category.
    (coproduct
      (morphisms category)
      (morphisms category)
      (morphisms category))
    (coproduct
      (objects category)
      (objects category))
    (fn [[i v]]
      (case i
        0 (list 0 (source-element category v))
        1 (list 1 (source-element category v))
        2 (list 0 (source-element category v))))
    (fn [[i v]]
      (case i
        0 (list 0 (target-element category v))
        1 (list 1 (target-element category v))
        2 (list 1 (target-element category v))))
    (fn [[[i v] [j w]]]
      (cond
        (or (= i j 0) (= i j 1)) (list i (category (list v w)))
        (and (= i 2) (= j 0)) (list 2 (category (list v w)))
        (and (= i 1) (= j 2)) (list 2 (category (list v w)))))
    (fn [[i v]]
      (list i (identity-morphism-of category v)))))

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

; Endotrivial categories
(defn endotrivial-category?
  [category]

  (and
    (category? category)
    (every?
      (fn [a]
        (= 1 (quiver-hom-cardinality category a a)))
      (objects category))))

(defn connected-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (<= (count (weak-connectivity (underlying-relation category))) 1)))

; Ontology of thin categories
(defmethod thin-category? :locus.elementary.copresheaf.core.protocols/semigroupoid
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
(defmethod thin-groupoid? :locus.elementary.copresheaf.core.protocols/semigroupoid
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

(defn n-diamond-category?
  [category]

  (and
    (thin-category? category)
    (let [rel (underlying-relation category)]
      (every?
        (fn [component]
          (diamond-relation? component))
        (weakly-connected-components rel)))))

; An attempt at describing cube categories
(defn cube-category?
  [category]

  (and
    (thin-category? category)
    (= (count (objects category)) 8)
    (boolean-algebra-relation? (underlying-relation category))))

; Special types of endotrivial categories
(defn skeletal-endotrivial-category?
  [category]

  (and
    (endotrivial-category? category)
    (antisymmetric? (underlying-relation category))))

(defn skeletal-thin-category?
  [category]

  (and
    (category? category)
    (posetal-quiver? (underlying-quiver category))))

(defmethod lattice? :locus.elementary.copresheaf.core.protocols/semigroupoid
  [x]

  (and
    (thin-category? x)
    (lattice-relation? (underlying-relation x))))

; Endomorphism only categories
(defmethod monoid? :locus.elementary.copresheaf.core.protocols/monoid
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

; Special classes of categories
(defmethod groupoid? :locus.elementary.copresheaf.core.protocols/semigroupoid
  [category]

  (or
    (isa? (type category) :locus.elementary.copresheaf.core.protocols/groupoid)
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