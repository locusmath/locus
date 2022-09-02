(ns locus.elementary.function.core.object
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.logic.order.seq :refer :all]
            [locus.elementary.relation.binary.product :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.incidence.system.setpart :refer :all]
            [locus.elementary.function.core.protocols :refer :all])
  (:import [locus.elementary.logic.base.core SeqableUniversal]))

; The topos Sets^(->) is the second most vital topos in our ontology, after the topos of Sets itself.
; This topos is the key to providing our whole new system of topos theoretic foundations, and
; its implementation as it motivates all our decisions about how we should create a topos
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
; is Robert Golbatt's Topoi the categorical analysis of logic.
(deftype SetFunction [in out func]
  AbstractMorphism
  (source-object [this] in)
  (target-object [this] out)

  StructuredDiset
  (first-set [this] in)
  (second-set [this] out)

  ConcreteMorphism
  (inputs [this] in)
  (outputs [this] out)

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

(derive SetFunction :locus.elementary.function.core.protocols/set-function)

; Underlying function of a concrete morphism
(defn underlying-function
  [func]

  (SetFunction. (inputs func) (outputs func) func))

; Generalized conversions
(defmulti to-function type)

(defmethod to-function :locus.elementary.function.core.protocols/set-function
  [func] func)

(defmethod to-function :default
  [func] (underlying-function func))

; Underlying transition of a morphism
(defn underlying-transition
  [morphism]

  (list (source-object morphism) (target-object morphism)))

; This is an interface between maps and functions
(defn mapfn
  [coll]

  (SetFunction.
    (set (keys coll))
    (set (vals coll))
    coll))

(defn fnmap
  [func]

  (let [coll (seq (inputs func))]
    (zipmap
      coll
      (map func coll))))

; This is a helpful tool for understanding functions
(defn function-triple
  [f]

  (list (inputs f) (outputs f) (fnmap f)))

; The underlying relation relates functions back to relations
(defmethod underlying-relation :default
  [func]

  (set
    (map
      (fn [i]
        (list i (func i)))
      (inputs func))))

(defn relation-to-function
  [rel]

  (when (single-valued-binary-relation? rel)
    (SetFunction.
      (relation-domain rel)
      (relation-codomain rel)
      (fn [i]
        (call rel i)))))

; Composition of functions
(defn compose-functions
  ([f] f)
  ([f g]
   (SetFunction.
     (inputs g)
     (outputs f)
     (comp f g)))
  ([f g & more] (reduce compose-functions (compose-functions f g) more)))

(defmethod compose* :locus.elementary.function.core.protocols/set-function
  [a b] (compose-functions a b))

; The identity function
(defn identity-function
  [a]

  (SetFunction. a a identity))

(defmethod identity-morphism :default
  [coll] (identity-function coll))

; Projection functions and inclusion functions
(defn inclusion-function
  [a b]

  (SetFunction. a b identity))

(defn projection-function
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

(defmethod product :locus.elementary.function.core.protocols/set-function
  [& args]

  (apply function-product args))

(defmethod coproduct :locus.elementary.function.core.protocols/set-function
  [& args]

  (apply function-coproduct args))

; The image and the kernel are fundamental invariants of a function
(defn function-image
  [func]

  (set (map func (inputs func))))

(defn function-kernel
  [func]

  (pn
    (fn [a b] (= (func a) (func b)))
    (inputs func)))

(defn kernel-image-factorisation
  [func]

  (list (function-kernel func) (function-image func)))

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

; We can take the image and inverse image functions
; on sets and turn them into functors
(defn image-functor
  [func]

  (SetFunction.
    (seqable-power-set (inputs func))
    (seqable-power-set (outputs func))
    (fn [coll]
      (set-image func coll))))

(defn inverse-image-functor
  [func]

  (SetFunction.
    (seqable-power-set (outputs func))
    (seqable-power-set (inputs func))
    (fn [coll]
      (set-inverse-image func coll))))

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

(defn function-selection
  [func]

  (SetFunction.
    (outputs func)
    natural-number?
    (fn [i]
      (fiber-cardinality func i))))

(defn output-multiset
  [func]

  (multiset (map func (inputs func))))

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

  (when (= (inputs a) (inputs b))
    (inclusion-function
      (equalizer a b)
      (inputs a))))

; Coequalizers are colimits of a parallel arrow diagram
(defn coequalizer
  [a b]

  (when (= (inputs a) (inputs b))
    (weak-connectivity
      (cl equivalence-relation?
         (set
           (map
             (fn [x]
               (list (a x) (b x)))
             (inputs a)))))))

(defn coequalizer-function
  [a b]

  (projection-function
    (coequalizer a b)))

; We can try to create conditions for dealing with fiber products
(defn fiber-product
  [f g]

  (filter
    (fn [[x y]]
      (= (f x) (g y)))
    (cartesian-product (inputs f) (inputs g))))

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

; Fiber products are categorically dual to fiber products
(defn fiber-coproduct
  [f g]

  (let [output (cartesian-coproduct (outputs f) (outputs g))]
    (set
      (map
        set
        (weak-connectivity
         (union
           (coreflexive-relation output)
           (set
             (map
               (fn [z]
                 (list
                   (list 0 (f z))
                   (list 1 (g z))))
               (inputs f)))))))))

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
        (isa? (type func) :locus.elementary.function.core.protocols/set-function)
        (in-hom-class? func a b)))))

(defn set-ev
  [a b]

  (->SetFunction
    (->BinaryCartesianProduct
      (internal-set-hom a b)
      a)
    b
    (fn [[func x]]
      (func x))))

; Subalgebras and congruences
; In the topos theoretic framework, objects of the topos of functions are
; associated to dual subalgebra and congruence lattices. The first deals with
; subfunctions defined by pairs of sets and the second is defined by i/o
; relations which we use to define the mathematics of dataflow analysis.
(defn subfunction?
  [func new-in new-out]

  (superset?
    (list (set-image func new-in) new-out)))

(defn subfunction
  [func new-in new-out]

  (SetFunction. new-in new-out func))

(defn restrict-function
  [func coll]

  (SetFunction. coll (outputs func) func))

(defn restrict-function-image
  [func coll]

  (SetFunction. (inputs func) coll func))

; Adjoin inputs to a mapping
(defmulti adjoin-inputs (fn [a b] (type a)))

; Adjoin outputs to a set function
(defmulti adjoin-outputs (fn [a b] (type a)))

(defmethod adjoin-outputs :locus.elementary.function.core.protocols/set-function
  [func coll]

  (SetFunction.
    (inputs func)
    (union (outputs func) coll)
    func))

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

; The induced inclusions of subfunctions
; This takes a given subfunction describes as a pair of subsets of the
; underlying transition and produces an inclusion over the inverse image.
(defn subfunction-to-inclusion
  [func new-in new-out]

  (inclusion-function
    new-in
    (set-inverse-image func new-out)))

; We now need something to deal with the enumeration of all
; possible subalgebras of a  given function.
(defn preceding-subalgebra?
  [func [a b] [c d]]

  (and (superset? (list a c))
       (superset? (list b d))))

(defn subalgebra-closure
  [func in-set out-set]

  [in-set (union out-set (set-image func in-set))])

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

; Quotients of functions are determined by I/O relations
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

(defn quotient-function
  [func in-partition out-partition]

  (SetFunction.
    in-partition
    out-partition
    (fn [in-part]
      (projection out-partition (func (first in-part))))))

; Enumeration of congruences of a function
(defn all-congruences
  [func]

  (set
    (mapcat
      (fn [in-partition]
        (let [current-image-partition (partition-image func in-partition)]
          (map
            (fn [out-partition]
              (list in-partition out-partition))
            (set-partition-coarsifications current-image-partition))))
      (enumerate-set-partitions (inputs func)))))

(defn function-quotients
  [func]

  (map
    (fn [[i o]]
      (quotient-function func i o))
    (all-congruences func)))

; We also need something to deal with the issue of congruence
; lattices of functions.
(defn preceding-congruence?
  [func [[in1 out1] [in2 out2]]]

  (and
    (set-superpartition? (list in1 in2))
    (set-superpartition? (list out1 out2))))

(defn congruence-closure
  [func in-partition out-partition]

  [in-partition (partitionize-family
                  (union
                    out-partition
                    (partition-image func in-partition)))])

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

; A function can be turned into a surjective, injective, or bijective
; function by certain subquotients in the topos of functions.
(defn injective-quotient
  [func]

  (restrict-function-image func (function-image func)))

(defn surjective-subobject
  [func]

  (SetFunction.
    (function-kernel func)
    (set (map (fn [i] #{i}) (outputs func)))
    (fn [part]
      #{(func (first part))})))

(defn bijective-subquotient
  [func]

  (surjective-subobject
    (surjective-subobject func)))

; The subobject classifier in the topos of sets
(defn subset-character
  [a b]

  (SetFunction.
    b
    #{false true}
    (fn [i]
      (contains? a i))))

; A partial ordering on functions related to the subobject ordering
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

(def superfunction?
  (assoc (->Universal
           (intersection
             seq?
             (fn [[a b]]
               (included-function? a b))))
    :arities #{2}))

; Ontology of functions
; The basic notion of a function is defined by the topos
; of functions, but then this concept can be further be
; restricted to a number of classes described here.
(defmulti set-function? type)

(defmethod set-function? :locus.elementary.function.core.protocols/set-function
  [obj] true)

(defmethod set-function? :default
  [obj] false)

(defn injective?
  [func]

  (distinct-seq? (map func (inputs func))))

(defn surjective?
  [func]

  (= (function-image func)
     (outputs func)))

(def invertible?
  (intersection
    injective?
    surjective?))

(defn endofunction?
  [func]

  (= (inputs func) (outputs func)))

(def autofunction?
  (intersection
    endofunction?
    invertible?))

(defn constant-function?
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

(defmethod inclusion-function? :locus.elementary.function.core.protocols/inclusion-function
  [func] true)

(defmethod inclusion-function? :locus.elementary.function.core.protocols/set-function
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

(defmethod intrinsic-identity-function? :locus.elementary.function.core.protocols/identity-function
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

; Visualizer
(defmethod visualize :locus.elementary.function.core.protocols/set-function
  [a]
  (visualize (underlying-relation a)))









