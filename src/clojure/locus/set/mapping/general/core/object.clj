(ns locus.set.mapping.general.core.object
  (:require [locus.set.logic.core.set :refer :all]
            [locus.set.logic.limit.product :refer :all]
            [locus.set.logic.structure.protocols :refer :all]
            [locus.con.core.object :refer :all]
            [locus.con.core.setpart :refer :all])
  (:import [locus.set.logic.core.set SeqableUniversal Multiset]
           (clojure.lang IPersistentMap IPersistentVector IPersistentList)
           (locus.set.logic.limit.product CartesianCoproduct)
           (locus.con.core.object CoproductPartition)))

; The topos Sets^(->) is the second most vital topos in our ontology, after the topos of Sets itself.
; This presheaf topos is the key to providing our whole new system of topos theoretic foundations,
; and its implementation as it motivates all our decisions about how we should create a topos
; theoretic ontology of computation and of algebra. The topos of functions supports the topos
; theoretic model of computation, by providing support for our model of dataflow. It supports
; the topos theoretic model of algebra by providing support for functions, and thereby
; allowing us to reduce questions about algebraic structures to questions about the individual
; functions that define them. In particular, we can reduce congruences on to the level of
; functions.

; Every object of a topos is naturally associated to both a subobject and a congruence lattice.
; We provide support for both logics on the level of individual functions, which in the true
; set of foundations allow us to build up everything to do with subobjects and congruences from
; our foundation in functions. These subobjects and congruences are related to their counterparts
; in the topos of Sets. In that case, subobjects are subsets and congruences are simply
; set partitions.

; Therefore a subobject of a function f: A -> B is an ordered pair of sets (I,O) such that I
; is a subset of A and O is a subset of B. A congruence of a function is an ordered pair
; (P,Q) of partitions with P partitioning A and Q partitioning B. Both of these must also
; satisfy extra conditions. In the first case, for a subobject (I,O) it must be the case that
; O contains the set image of I. We generalize this for ordered pairs of partitions (P,Q)
; by defining the partition image so that a congruence (P,Q) is an ordered partition such
; that Q contains the partition image of P.

; We have selected the partition image terminology to maintain consistency with the notion of
; a set image and to emphasize the duality between them. We are familiar with no explanation
; of the fundamental notion of a congruence of a function in existing literature, so that
; is the terminology we are going with right now. A congruence of a function (P,Q) is one
; for which equality with respect to P determines equality with respect to Q, this
; naturally always produces a quotient function between partitions.

; This basic notion of a congruence of a function plays a decisive role in our selection
; of topos theory as a tool for mathematical modelling computation because it  allows
; us to effectively model dataflow dependencies. This plays a central role in our
; research into defining a local geometry of computation. We believe that topos theory
; provides the best model of computation and that is a great organizing project
; for this entire project, which bears topos theory in its name.

; In addition to what we believe is the best model of computation available, topos
; theory also has exciting implications in algebraic geometry including those closer to
; Grothendeick's original papers: such as the theory of toposes of sheaves over a site.
; These other topoi should also be fundamental objects of our research. A good reference on
; some other aspects of the topos of functions Sets^(->) such as its subobject classifier
; is Robert Goldblatt's Topoi the categorical analysis of logic.

(deftype SetFunction [in out func]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

  ConcreteObject
  (underlying-set [this] (CartesianCoproduct. [in out]))

  Object
  (equals [this b]
    (and
      (equal-universals? in (inputs b))
      (equal-universals? out (outputs b))
      (every?
        (fn [i]
          (= (func i) (b i)))
        in)))

  clojure.lang.IFn
  (invoke [this obj]
    (func obj))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive SetFunction :locus.set.logic.structure.protocols/set-function)

(defmethod visualize :locus.set.logic.structure.protocols/structured-function
  [func]

  (let [in-count (count (inputs func))
        out-count (count (outputs func))
        in-seq (seq (inputs func))
        out-seq (seq (outputs func))
        out-inverse-mapping (zipmap
                              out-seq
                              (range (count out-seq)))]
    (visualize-graphviz-file*
      true
      "LR"
      [(range in-count)
       (range in-count (+ in-count out-count))]
      (set
        (map-indexed
          (fn [i v]
            (list i (+ in-count (out-inverse-mapping (func v)))))
          in-seq))
      true
      (vec (concat in-seq out-seq)))))

; Get the sets and functions associated with a set function
(defn identity-function
  [a]

  (SetFunction. a a identity))

(defmethod identity-morphism :locus.set.logic.core.set/universal
  [coll] (identity-function coll))

(defmethod get-set :locus.set.logic.structure.protocols/set-function
  [f x]

  (case x
    0 (inputs f)
    1 (outputs f)))

(defmethod get-function :locus.set.logic.structure.protocols/set-function
  [f [a b]]

  (case [a b]
    [0 0] (identity-function (inputs f))
    [1 1] (identity-function (outputs f))
    [0 1] f))

(defmethod get-set :locus.set.logic.core.set/universal
  [coll x] (case x 0 coll))

(defmethod get-function :locus.set.logic.core.set/universal
  [coll [a b]] (case [a b] [0 0] (identity-function coll)))

; Specific conversion routines
(defn mapfn
  [coll]

  (SetFunction.
    (set (keys coll))
    (set (vals coll))
    coll))

(defn vector-to-function
  [vec]

  (->SetFunction
    (->Upto (count vec))
    (set vec)
    (fn [i]
      (nth vec i))))

(defn relation-to-function
  [coll]

  (let [domain (set (map first coll))
        codomain (set (map second coll))]
    (SetFunction.
      domain
      codomain
      (fn [x]
        (first
          (for [[a b] coll
                :when (= a x)]
            b))))))

(defn underlying-function
  [func]

  (SetFunction. (inputs func) (outputs func) func))

; General conversion routines
(defmulti to-function type)

(defmethod to-function :locus.set.logic.structure.protocols/set-function
  [func] func)

(defmethod to-function IPersistentMap
  [func] (mapfn func))

(defmethod to-function IPersistentVector
  [coll] (vector-to-function coll))

(defmethod to-function :locus.set.logic.core.set/universal
  [rel] (relation-to-function rel))

(defmethod to-function :default
  [func] (underlying-function func))

; Composition in the topos Sets of sets and functions
; This is the most familiar composition operation in mathematics.
(defn compose-functions
  ([f] f)
  ([f g]
   (SetFunction.
     (inputs g)
     (outputs f)
     (comp f g)))
  ([f g & more] (reduce compose-functions (compose-functions f g) more)))

(defmethod compose* :locus.set.logic.structure.protocols/set-function
  [a b] (compose-functions a b))

; The images and inverse images of functions are one of the basic
; computations we can perform with them
(defn set-image
  [func coll]

  (set (map func coll)))

(defn set-inverse-image
  [func coll]

  (set
    (filter
      (fn [i]
        (coll (func i)))
      (inputs func))))

(defn partition-image
  [func partition]

  (partitionize-family
    (set
      (map
        (fn [part]
          (set-image func part))
        partition))))

(defn partition-inverse-image
  [func partition]

  (set
    (for [i partition
          :let [coll (set-inverse-image func i)]
          :when (not (empty? coll))]
      coll)))

; Generic images and inverse images
(defmulti image (fn [a b] [(type a) (type b)]))

(defmethod image
  [:locus.set.logic.structure.protocols/set-function
   :locus.set.logic.core.set/universal]
  [func coll]

  (set (map func coll)))

(defmethod image
  [:locus.set.logic.structure.protocols/set-function
   :locus.con.core.object/set-partition]
  [func partition]

  (->SetPartition
    (partition-image func (equivalence-classes partition))))

(defmulti inverse-image (fn [a b] [(type a) (type b)]))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function
   :locus.set.logic.core.set/universal]
  [func coll]

  (set-inverse-image func coll))

(defmethod inverse-image
  [:locus.set.logic.structure.protocols/set-function
   :locus.con.core.object/set-partition]
  [func partition]

  (->SetPartition
    (partition-inverse-image func (equivalence-classes partition))))

(defmethod image
  [:locus.set.logic.structure.protocols/set-function Multiset]
  [func coll]

  (umap func coll))

; The function image of a function is the set image of its domain
(defn function-image
  [func]

  (set (map func (inputs func))))

; The kernel of a function is the partition image of the minimal partition of its codomain
(defn kernel
  [func]

  (->FunctionalPartition (inputs func) func))

(defn function-kernel
  [func]

  (pn
    (fn [a b] (= (func a) (func b)))
    (inputs func)))

; Epi mono factorisations in the topos of functions
(defn kernel-image-factorisation
  [func]

  (list (function-kernel func) (function-image func)))

; Get the selection of a function by the fiber cardinalities
(defn fiber
  [func elem]

  (set-inverse-image func #{elem}))

(defn fiber-cardinality
  [func elem]

  (count (fiber func elem)))

(defn fiber-cardinalities
  [func]

  (add (umap count (function-kernel func))
       (repeat-multiset (count (difference (outputs func) (function-image func))) 0)))

(defn output-multiset
  [func]

  (multiset (map func (inputs func))))

(defn function-selection
  [func]

  (SetFunction.
    (outputs func)
    (set (fiber-cardinalities func))
    (fn [i]
      (fiber-cardinality func i))))

(defn fiber-valued-mapping
  [func]

  (loop [coll (seq (inputs func))
         seen-outputs #{}
         mapping {}]
    (if (empty? coll)
      mapping
      (let [current-elem (first coll)
            current-output (func current-elem)]
        (if (contains? seen-outputs current-output)
          (recur
            (rest coll)
            seen-outputs
            (assoc mapping current-output (conj (get mapping current-output) current-elem)))
          (recur
            (rest coll)
            (conj seen-outputs current-output)
            (conj mapping [current-output #{current-elem}])))))))

; Let f: A -> B be a function then f^C : B -> A is a relation rather than an ordinary function.
; However, as a relation it has an inverse image. This forms an alternative adjunction to the
; familiar image/inverse image adjunction. This adjunction takes the converse relation image
; and the converse relation inverse image as its adjoints.
(defn fiber-inverse-image
  [func coll]

  (set
    (filter
      (fn [output]
        (superset? (list (fiber func output) coll)))
      (outputs func))))

; Kernel classes in functions
(defn kernel-class-of
  [func x]

  (fiber func (func x)))

; Underlying relations of set functions
(defmethod underlying-relation :locus.set.logic.structure.protocols/structured-function
  [func]

  (set
    (map
      (fn [i]
        (list i (func i)))
      (inputs func))))

; Underlying maps of set functions
(defn underlying-map
  [func]

  (let [coll (seq (inputs func))]
    (zipmap
      coll
      (map func coll))))

; Functions can be treated as special types of ordered triples
(defn underlying-transition
  [morphism]

  (list (source-object morphism) (target-object morphism)))

(defn function-triple
  [f]

  (list (inputs f) (outputs f) (underlying-map f)))

; Projection functions and inclusion functions
(defn inclusion-function
  [a b]

  (SetFunction. a b identity))

(defmulti projection-function type)

(defmethod projection-function :locus.con.core.object/set-partition
  [partition]

  (SetFunction.
    (underlying-set partition)
    (equivalence-classes partition)
    (fn [i]
      (equivalence-class-of partition i))))

(defmethod projection-function :default
  [partition]

  (SetFunction.
    (apply union partition)
    partition
    (partial projection partition)))

; Iterative application is an alternative to using repeated composition
(defn iteratively-apply
  [f n arg]

  (loop [i n
         cval arg]
    (if (<= i 0)
      cval
      (recur
        (dec i)
        (f cval)))))

; Numeric properties of functions
(defn function-signature
  [func]

  (map count (function-kernel func)))

(defn function-order
  [func]

  (count (function-image func)))

(defn function-inputs-size
  [func]

  (count (inputs func)))

(defn function-outputs-size
  [func]

  (count (inputs func)))

(defn function-cardinality
  [func]

  (+ (count (inputs func))
     (count (outputs func))))

(defn nonsurjectivity
  [func]

  (- (count (outputs func)) (count (function-image func))))

; Adjoin inputs and outputs to a mapping
(defmulti adjoin-inputs (fn [a b] (type a)))

(defmulti adjoin-outputs (fn [a b] (type a)))

(defmethod adjoin-outputs :locus.set.logic.structure.protocols/set-function
  [func coll]

  (SetFunction.
    (inputs func)
    (union (outputs func) coll)
    func))

(defn funassoc
  [func & items]

  (let [coll (apply hash-map items)
        key-set (set (keys coll))
        val-set (set (vals coll))]
    (->SetFunction
      (union (inputs func) key-set)
      (union (outputs func) val-set)
      (fn [i]
        (if (contains? key-set i)
          (get coll i)
          (func i))))))

(defn merge-functions
  ([] (SetFunction. #{} #{} (constantly nil)))
  ([a] a)
  ([a b]
   (let [a-keys (inputs a)
         b-keys (inputs b)]
     (->SetFunction
      (union a-keys b-keys)
      (union (outputs a) (outputs b))
      (fn [i]
        (if (contains? b-keys i)
          (b i)
          (a i))))))
  ([a b & args]
   (reduce merge-functions (merge-functions a b) args)))

; Limits and colimits in the topos of copresheaves
; Several limits and colimits of copresheaves are so fundamental that they have their own names and
; special implementations. These include equalizers, coequalizers, product, coproducts, and their
; variants like fiber products and fiber coproducts. All limits and colimits of copresheaves can be
; formed from equalizers, coequalizers, products, and coproducts.

; Equalizers are limits of a parallel arrow diagram
(defn equalizer
  [a b]

  (when (= (inputs a) (inputs b))
    (filter
      (fn [x]
        (= (a x) (b x)))
      (inputs a))))

(defn equalizer-function
  [a b]

  (inclusion-function
    (equalizer a b)
    (inputs a)))

; Coequalizers are colimits of a parallel arrow diagram
(defn coequalizer
  [a b]

  (when (= (inputs a) (inputs b))
    (let [common-inputs (inputs a)]
      (partitionize-family
        (set
          (map
            (fn [x]
              (set (list (a x) (b x))))
            common-inputs))))))

(defn coequalizer-function
  [a b]

  (projection-function
    (coequalizer a b)))

; We can try to create conditions for dealing with fiber products
(defn fiber-product
  [f g]

  (set
    (filter
      (fn [[x y]]
        (= (f x) (g y)))
      (cartesian-product (inputs f) (inputs g)))))

(defn fiber-product-projections
  [f g]

  (let [fiber-product-object (fiber-product f g)
        first-input (inputs f)
        second-input (inputs g)]
    (list
      (SetFunction.
        fiber-product-object
        first-input
        (fn [x]
          (first x)))
      (SetFunction.
        fiber-product-object
        second-input
        (fn [x]
          (second x))))))

; Fiber coproducts are categorically dual to fiber products
(defn fiber-coproduct
  [f g]

  (let [output (cartesian-coproduct (outputs f) (outputs g))]
    (partitionize-family
      (union
        (set (map (fn [i] #{i}) output))
        (set
          (map
            (fn [z]
              (set
                (list
                  (list 0 (f z))
                  (list 1 (g z)))))
            (inputs f)))))))

(defn fiber-coproduct-projections
  [f g]

  (let [fiber-coproduct-object (fiber-coproduct f g)
        first-output (outputs f)
        second-output (outputs g)]
    (list
      (SetFunction.
        first-output
        fiber-coproduct-object
        (fn [x]
          (projection fiber-coproduct-object (list 0 x))))
      (SetFunction.
        second-output
        fiber-coproduct-object
        (fn [x]
          (projection fiber-coproduct-object (list 1 x)))))))

; Product and coproduct of functions
(defn function-product
  [& functions]

  (SetFunction.
    (apply cartesian-product (map inputs functions))
    (apply cartesian-product (map outputs functions))
    (fn [coll]
      (map-indexed
        (fn [i v]
          ((nth functions i) v))
        coll))))

(defn function-coproduct
  [& functions]

  (SetFunction.
    (apply cartesian-coproduct (map inputs functions))
    (apply cartesian-coproduct (map outputs functions))
    (fn [[i v]]
      (list i ((nth functions i) v)))))

(defmethod product :locus.set.logic.structure.protocols/set-function
  [& args]

  (apply function-product args))

(defmethod coproduct :locus.set.logic.structure.protocols/set-function
  [& args]

  (apply function-coproduct args))

; A topos like Sets is identified by the fact that it has all limits and colimits for all
; diagrams. In addition to this, it must have internal homs and evaluation morphisms so that
; it is a closed category. To complete this implementation of the fundamental topos Sets
; we implement an internal hom for it.

; An evaluation arrow as a set function
(defn in-hom-class?
  [func a b]

  (and
    (equal-universals? (inputs func) a)
    (equal-universals? (outputs func) b)))

(defn internal-set-hom
  [a b]

  (->Universal
    (fn [func]
      (and
        (isa? (type func) :locus.set.logic.structure.protocols/set-function)
        (in-hom-class? func a b)))))

(defn set-ev
  [a b]

  (->SetFunction
    (->CartesianProduct
      [(internal-set-hom a b)
       a])
    b
    (fn [[func x]]
      (func x))))

; The subobject classifier in the topos of sets
(defn subset-character
  [a b]

  (SetFunction.
    b
    #{false true}
    (fn [i]
      (contains? a i))))

; Special restriction methods for functions
(defn subfunction
  [func new-in new-out]

  (SetFunction. new-in new-out func))

(defn restrict-function
  [func coll]

  (SetFunction.
    coll
    (outputs func)
    func))

(defn restrict-function-image
  [func coll]

  (SetFunction.
    (inputs func)
    coll
    func))

(defn remove-function-input
  [func x]

  (SetFunction.
    (disj (inputs func) x)
    (outputs func)
    func))

(defn remove-function-inputs
  [func coll]

  (SetFunction.
    (difference (inputs func) coll)
    (outputs func)
    func))

(defn remove-function-output
  [func x]

  (subfunction
    func
    (difference (inputs func) (fiber func x))
    (disj (outputs func) x)))

(defn remove-function-outputs
  [func coll]

  (subfunction
    func
    (difference (inputs func) (set-inverse-image func coll))
    (difference (outputs func) coll)))

; Testing for subalgebras
(defn subfunction?
  [func new-in new-out]

  (superset?
    (list (set-image func new-in) new-out)))

(defmethod subalgebra?
  [:locus.set.logic.structure.protocols/set-function
   CartesianCoproduct]
  [func coll]

  (let [colls (.-colls coll)]
    (and
      (= (count colls) 2)
      (let [[x y] colls]
        (subfunction? func x y)))))

(defmethod subalgebra?
  [:locus.set.logic.structure.protocols/set-function
   :locus.set.logic.core.set/universal]
  [func coll]

  (and
    (every? (fn [i] (and (seqable? i) (= (count i) 2))) coll)
    (let [first-elements (set
                           (for [[i v] coll
                                 :when (= i 0)]
                             v))
          second-elements (set
                            (for [[i v] coll
                                  :when (= i 1)]
                              v))]
      (subfunction? func first-elements second-elements))))

; Getting subobjects of functions
(defmethod substructure
  [:locus.set.logic.structure.protocols/set-function
   CartesianCoproduct]
  [func coll]

  (let [[x y] (.-colls coll)]
    (subfunction func x y)))

(defmethod substructure
  [:locus.set.logic.structure.protocols/set-function
   :locus.set.logic.core.set/universal]
  [func coll]

  (let [first-elements (set
                         (for [[i v] coll
                               :when (= i 0)]
                           v))
        second-elements (set
                          (for [[i v] coll
                                :when (= i 1)]
                            v))]
    (subfunction func first-elements second-elements)))

; This is an attempt to deal with the enumeration of subalgebras
(defn number-of-subalgebras
  [nms]

  (apply
    *
    (map
      (comp inc power-of-two)
      nms)))

(defn enumerate-subalgebras
  [func]

  (mapcat
    (fn [i]
      (let [current-image (set-image func i)]
        (map
          (fn [j]
            (list i (union current-image j)))
          (power-set
            (difference (outputs func) current-image)))))
    (seqable-power-set (inputs func))))

(defn all-subalgebras
  [func]

  (SeqableUniversal.
    (fn [[a b]]
      (subfunction? func a b))
    (enumerate-subalgebras func)
    {:count (number-of-subalgebras (fiber-cardinalities func))}))

(defn function-subobjects
  [func]

  (map
    (fn [[i o]]
      (subfunction func i o))
    (enumerate-subalgebras func)))

; Closure and interior of subalgebras
(defn subalgebra-closure
  [func in-set out-set]

  [in-set (union out-set (set-image func in-set))])

(defn subalgebra-interior
  [func in-set out-set]

  [(intersection in-set (set-inverse-image func out-set)) out-set])

; Heyting algebra structure on subobjects of functions
(defn subfunction-implication
  [func [u1 u2] [v1 v2]]

  (let [cu1 (difference (inputs func) u1)
        cu2 (difference (outputs func) u2)
        a (union cu1 v1)
        b (union cu2 v2)]
    (subalgebra-interior func a b)))

; We now need something to deal with the enumeration of all
; possible subalgebras of a  given function.
(defn preceding-subalgebra?
  [func [a b] [c d]]

  (and (superset? (list a c))
       (superset? (list b d))))

(defn parent-subalgebras
  [func in-set out-set]

  (set
    (map
      (fn [[a b]]
        [(union in-set a) (union out-set
                                 b
                                 (set-image func a))])
      (cartesian-product
        (power-set (difference (inputs func) in-set))
        (power-set (difference (outputs func) out-set))))))

(defn subalgebras-relation
  [func]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (parent-subalgebras func in-set out-set)))
      (all-subalgebras func))))

(defn covering-additions
  [func in-set out-set]

  [(set
     (filter
       (fn [i]
         (contains? out-set (func i)))
       (difference (inputs func) in-set)))
   (difference (outputs func) out-set)])

(defn covering-subalgebras
  [func in-set out-set]

  (let [[inputs-additions outputs-additions] (covering-additions func in-set out-set)]
    (union
      (set
        (map
          (fn [i]
            [(conj in-set i) out-set])
          inputs-additions))
      (set
        (map
          (fn [i]
            [in-set (conj out-set i)])
          outputs-additions)))))

(defn subalgebras-covering
  [func]

  (set
    (mapcat
      (fn [[in-set out-set]]
        (map
          (fn [[new-in-set new-out-set]]
            (list [in-set out-set] [new-in-set new-out-set]))
          (covering-subalgebras func in-set out-set)))
      (all-subalgebras func))))

; The induced inclusions of subfunctions
; This takes a given subfunction describes as a pair of subsets of the
; underlying transition and produces an inclusion over the inverse image.
(defn subfunction-to-inclusion
  [func new-in new-out]

  (inclusion-function
    new-in
    (set-inverse-image func new-out)))

; Testing for io-relations
(defn io-relation?
  [func in-partition out-partition]

  (let [out-relation (equivalence-relation out-partition)]
    (every?
      (fn [in-part]
        (let [current-image (set-image func in-part)]
          (every?
            (fn [[a b]]
              (out-relation (list a b)))
            (cartesian-power current-image 2))))
      in-partition)))

(defmethod congruence?
  [:locus.set.logic.structure.protocols/set-function, CoproductPartition]
  [func partition]

  (let [partitions (.-partitions partition)
        [p q] partitions]
    (io-relation? func (equivalence-classes p) (equivalence-classes q))))

; Quotients
(defn quotient-function
  [func in-partition out-partition]

  (SetFunction.
    in-partition
    out-partition
    (fn [in-part]
      (projection out-partition (func (first in-part))))))

(defmethod quotient
  [:locus.set.logic.structure.protocols/set-function, CoproductPartition]
  [func partition]

  (let [partitions (.-partitions partition)
        [p q] partitions]
    (quotient-function func (equivalence-classes p) (equivalence-classes q))))

; Enumeration of congruences of a function
(defn all-congruences
  [func]

  (let [non-image-singletons (set
                               (map
                                 (fn [i]
                                   #{i})
                                 (difference (outputs func) (function-image func))))]
    (set
     (mapcat
       (fn [in-partition]
         (let [current-image-partition (union
                                         non-image-singletons
                                         (partition-image func in-partition))]
           (map
             (fn [out-partition]
               (list in-partition out-partition))
             (set-partition-coarsifications current-image-partition))))
       (enumerate-set-partitions (inputs func))))))

(defn function-quotients
  [func]

  (map
    (fn [[i o]]
      (quotient-function func i o))
    (all-congruences func)))

; Relations on the set of congruences
(defn preceding-congruence?
  [func [[in1 out1] [in2 out2]]]

  (and
    (set-superpartition? (list in1 in2))
    (set-superpartition? (list out1 out2))))

(defn covering-congruences
  [func in-partition out-partition]

  (union
    (set
      (map
        (fn [new-out-partition]
          (list in-partition new-out-partition))
        (direct-set-partition-coarsifications out-partition)))
    (set
      (for [i (direct-set-partition-coarsifications in-partition)
            :when (set-superpartition?
                    (list (partition-image func i) out-partition))]
        (list i out-partition)))))

(defn congruences-covering
  [func]

  (set
    (mapcat
      (fn [[in-partition out-partition]]
        (map
          (fn [[new-in-partition new-out-partition]]
            (list [in-partition out-partition] [new-in-partition new-out-partition]))
          (covering-congruences func in-partition out-partition)))
      (all-congruences func))))

(defn congruence-closure
  [func in-partition out-partition]

  [in-partition (partitionize-family
                  (union
                    out-partition
                    (partition-image func in-partition)))])

; Surjective components of the subalgebra lattice
; Set images are simply a way of getting surjective subobjects.
(defn surjective-subalgebra
  [func]

  (list (inputs func) (function-image func)))

(defn surjective-subalgebra-by
  [func coll]

  (list coll (set-image func coll)))

(defn surjective-subfunction
  [func]

  (restrict-function-image func (function-image func)))

(defn surjective-subfunction-by
  [func coll]

  (subfunction
    func
    coll
    (set-image func coll)))

; Injective components of the congruence lattice
; Partition inverse images are simply a way of getting injective quotients.
(defn injective-congruence
  [func]

  (list
    (function-kernel func)
    (set
      (map
        (fn [i]
          #{i})
        (outputs func)))))

(defn injective-congruence-by
  [func out-partition]

  (list
    (partition-inverse-image func out-partition)
    out-partition))

(defn injective-quotient
  [func]

  (SetFunction.
    (function-kernel func)
    (outputs func)
    (fn [part]
      (func (first part)))))

(defn injective-quotient-by
  [func out-partition]

  (quotient-function
    func
    (partition-inverse-image func out-partition)
    out-partition))

; Bijective subquotients
(defn bijective-subquotient
  [func]

  (injective-quotient
    (surjective-subfunction func)))

; Full subobjects
(defn full-subfunction
  [func output-set]

  (subfunction
    func
    (set-inverse-image func output-set)
    output-set))

; Full quotients
(defn full-quotient-function
  [func in-partition]

  (quotient-function
    func
    in-partition
    (partition-image func in-partition)))

; The empty component of a function
(defn empty-subfunction
  [func]

  (inclusion-function #{} (outputs func)))

; Every function is associated to a constant quotient function
(defn constant-quotient-function
  [func]

  (quotient-function
    func
    (set
      (map
        (fn [i]
          #{i})
        (inputs func)))
    #{(outputs func)}))

; Check if elements are contained in the input or output set
(defn contains-input?
  [func x]

  (contains? (inputs func) x))

(defn contains-output?
  [func x]

  (contains? (outputs func) x))

(defn contains-inputs?
  [func coll]

  (superset? (list coll (inputs func))))

(defn contains-outputs?
  [func coll]

  (superset? (list coll (outputs func))))

; Ontology of relations
; Functions may be related to one another by a number of different relations including
; equality and ordering.
(defn included-function?
  [a b]

  (and
    (superset? (list (inputs a) (inputs b)))
    (superset? (list (outputs a) (outputs b)))
    (every?
      (fn [i]
        (= (a i) (b i)))
      (inputs a))))

(defn equal-functions?
  [a b]

  (and
    (equal-universals? (inputs a) (inputs b))
    (equal-universals? (outputs a) (outputs b))
    (every?
      (fn [i]
        (= (a i) (b i)))
      (inputs a))))

(defn glueable-functions?
  [a b]

  (and
    (equal-universals? (inputs a) (inputs b))
    (equal-universals? (outputs a) (outputs b))
    (every?
      (fn [i]
        (= (a i) (b i)))
      (intersection (inputs a) (inputs b)))))

(def superfunction?
  (assoc (->Universal
           (intersection
             seq?
             (fn [[a b]]
               (included-function? a b))))
    :arities #{2}))

; Ontology of set functions
; In our basic implementation of the topos of Sets, we consider functions to be morphisms of sets,
; but that is not the whole picture provided by topos theory. It also happens that, furthermore,
; Sets are objects of the concrete topos Sets^(->) with their own morphisms between them, which
; the basis of a lot of understanding of set functions.
(defmulti set-function? type)

(defmethod set-function? :locus.set.logic.structure.protocols/set-function
  [obj] true)

(defmethod set-function? :default
  [obj] false)

(defmulti injective? type)

(defmethod injective? :locus.set.logic.structure.protocols/injective-set-function
  [func] true)

(defmethod injective? :default
  [func]

  (and
    (set-function? func)
    (let [kernel-classes (function-kernel func)]
      (every?
        (fn [i]
          (= (count i) 1))
        kernel-classes))))

(defmulti surjective? type)

(defmethod surjective? :locus.set.logic.structure.protocols/surjective-set-function
  [func] true)

(defmethod surjective? :default
  [func]

  (and
    (set-function? func)
    (equal-universals?
      (function-image func)
      (outputs func))))

(defmulti invertible? type)

(defmethod invertible? :locus.set.logic.structure.protocols/invertible-set-function
  [func] true)

(defmethod invertible? :default
  [func]

  (and
    (injective? func)
    (surjective? func)))

(defmulti endofunction? type)

(defmethod endofunction? :locus.set.logic.structure.protocols/transformation
  [func] true)

(defmethod endofunction? :default
  [func]

  (and
    (set-function? func)
    (equal-universals?
      (inputs func)
      (outputs func))))

(defmulti autofunction? type)

(defmethod autofunction? :locus.set.logic.structure.protocols/permutation
  [func] true)

(defmethod autofunction? :default
  [func]

  (and
    (endofunction? func)
    (invertible? func)))

; Other classes of functions
(defn constant-function?
  [func]

  (= (count (function-kernel func)) 1))

(defn surjective-constant-function?
  [func]

  (= (count (function-image func)) 1))

(defn element-function?
  [func]

  (= (count (inputs func)) 1))

(defn ordered-pair-function?
  [func]

  (and
    (= (count (inputs func))
       (count (outputs func))
       1)))

(def loop-function?
  (intersection
    ordered-pair-function?
    endofunction?))

(defn idempotent-function?
  [func]

  (every?
    (fn [i]
      (= (func (func i)) (func i)))
    (inputs func)))

(defn involution-function?
  [func]

  (every?
    (fn [i]
      (= (func (func i)) i))
    (inputs func)))

(defn empty-inclusion-function?
  [func]

  (empty? (inputs func)))

(defmulti inclusion-function? type)

(defmethod inclusion-function? :locus.set.logic.structure.protocols/inclusion-function
  [func] true)

(defmethod inclusion-function? :locus.set.logic.structure.protocols/set-function
  [func]

  (and
    (superset? (list (inputs func) (outputs func)))
    (every?
      (fn [i]
        (= (func i) i))
      (inputs func))))

(defmethod inclusion-function? :default
  [func] false)

(defmulti identity-function? type)

(defmethod identity-function? :default
  [func]

  (and
    (inclusion-function? func)
    (endofunction? func)))

(defmulti intrinsic-identity-function? type)

(defmethod intrinsic-identity-function? :locus.set.logic.structure.protocols/identity-function
  [func] true)

(defmethod intrinsic-identity-function? :default
  [func] false)

; The properties ontology of functions
(defn !=functions
  [f g]

  (not (= f g)))

(defn !=function-underlying-transition
  [f g]

  (not= (underlying-transition f)
        (underlying-transition g)))

(defn !=function-inputs
  [f g]

  (not= (inputs f) (inputs g)))

(defn !=function-outputs
  [f g]

  (not= (inputs f) (outputs g)))

(defn !=function-inputs-size
  [f g]

  (not= (count (inputs f)) (count (inputs g))))

(defn !=function-outputs-size
  [f g]

  (not= (count (inputs f)) (count (outputs g))))

(defn !=function-kernel
  [f g]

  (not= (function-kernel f) (function-kernel g)))

(defn !=function-image
  [f g]

  (not= (function-image f) (function-image g)))

(defn !=function-order
  [f g]

  (not= (function-order f) (function-order g)))

(defn !=function-isomorphism-type
  [f g]

  (not= (fiber-cardinalities f) (fiber-cardinalities g)))
