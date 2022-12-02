(ns locus.mapping.multivalued.hyperfunction
  (:require [locus.base.logic.core.set :refer :all]
            [locus.base.logic.limit.product :refer :all]
            [locus.base.function.image.image-function :refer :all]
            [locus.base.function.core.object :refer :all]
            [locus.base.invertible.function.object :refer :all]
            [locus.base.logic.structure.protocols :refer :all]
            [locus.base.partition.core.object :refer [projection]])
  (:import (locus.base.function.core.object SetFunction)
           (clojure.lang IPersistentMap)
           (locus.base.function.image.image_function ImageFunction)))

; Hyperfunctions:
; The category Rel of sets and relations does not form an elementary topos. As a consequence,
; it lacks many of the desirable features of a topos. In order to get around this, we represent
; Rel as a concrete subcategory of Sets consisting of image functions, where an image
; function is a complete union homomorphism of power sets. The category Rel can then be
; embedded in the topos Sets, with reference to this special class of functions.

; In our implementation of multivalued relations, you can convert a multivalued function into an
; image function by using the to-function method. In the other direction, we provide the
; singleton-images-relation function to convert a member of the image functions class
; into a multivalued function. This lets us transfer back and forth between the category Rel
; and the topos Sets.

; While a multivalued function in Rel is primarily related to an image function of power
; sets, another classes of functions corresponds to hyperfunctions: the set valued
; functions produced by singleton images. This correspondence states that a multivalued
; function from A to B is like a function from A to the power set of B. As a consequence,
; hyperfunctions implement the clojure.lang.IFn interface in such a manner that
; the application of an element a is the set of elements b that form ordered pairs
; in the multivalued function.

; Multivalued functions are important in the topos theoretic foundations of computing
; as a means of defining an abstraction layer over the topoi of sets and functions.
; Therefore, the terminology that we use in much of this file is determined by the
; needs of topos theory. In particular, we use make the definition of the hyperfunction
; image and inverse image correspond to the definitions of partition images and
; inverse images used in the topos theoretic models of dataflow. The converse image
; is then defined separately from the relational inverse image.

; These concepts allow us to define a subalgebra lattice of a hyperfunction, which
; is the lattice that is mapped into the lattice of congruences of a function.
; This subalgebra lattice is basically implemented in the lattice folder. It restores
; the subobject lattice of a function in the special case in which a function is
; expressed as a hyperfunction.
(deftype Hyperfunction [source target func]
  AbstractMorphism
  (source-object [this] source)
  (target-object [this] target)

  clojure.lang.IFn
  (invoke [this arg]
    (func arg))
  (applyTo [this args]
    (clojure.lang.AFn/applyToHelper this args)))

(derive Hyperfunction :locus.base.logic.structure.protocols/structured-function)

(defmethod to-function Hyperfunction
  [^Hyperfunction rel]

  (ImageFunction.
    (.source rel)
    (.target rel)
    (.func rel)))

; Underlying relations of visualisation of hyperfunctions
(defmethod underlying-relation Hyperfunction
  [rel]

  (apply
    union
    (map
      (fn [input]
        (set
          (map
            (fn [i]
              (list input i))
            (rel input))))
      (source-object rel))))

(defmethod visualize Hyperfunction
  [rel]

  (let [p {0 (source-object rel)
           1 (target-object rel)}
        v (set
            (map
              (fn [[a b]]
                (list (list 0 a) (list 1 b)))
              (underlying-relation rel)))]
    (visualize-clustered-digraph* "LR" p v)))

; Hyperfunctions form a category Rel of sets and hyperfunctions
(defmethod compose* Hyperfunction
  [a b]

  (Hyperfunction.
    (source-object b)
    (target-object a)
    (fn [x]
      (apply union (map a (b x))))))

(defn identity-hyperfunction
  [coll]

  (Hyperfunction.
    coll
    coll
    (fn [i] #{i})))

; Conversion mechanisms for hyperfunctions
(defmulti to-hyperfunction type)

(defmethod to-hyperfunction Hyperfunction
  [rel] rel)

(defmethod to-hyperfunction :locus.base.logic.core.set/universal
  [rel]

  (Hyperfunction.
    (set (map first rel))
    (set (map second rel))
    (fn [x]
      (set (for [[a b] rel
                 :when (= a x)]
             b)))))

(defmethod to-hyperfunction :locus.base.logic.structure.protocols/set-function
  [func]

  (Hyperfunction.
    (inputs func)
    (outputs func)
    (fn [x]
      #{(func x)})))

(defmethod to-hyperfunction IPersistentMap
  [coll]

  (Hyperfunction.
    (set (keys coll))
    (set (vals coll))
    (fn [i]
      #{(get coll i)})))

; Hyperclosed sets and their adjunction
(defn hyperclosed-set?
  [hyperfunction source target]

  (every?
    (fn [source-element]
      (superset? (list (hyperfunction source-element) target)))
    source))

(defn hyperfunction-set-image
  [hyperfunction coll]

  (apply
    union
    (map
      (fn [i]
        (hyperfunction i))
      coll)))

(defn hyperfunction-set-inverse-image
  [hyperfunction coll]

  (set
    (filter
      (fn [source-element]
        (superset? (list (hyperfunction source-element) coll)))
      (source-object hyperfunction))))

(defn hyperfunction-closed-sets
  [rel]

  (let [in (source-object rel)
        out (target-object rel)]
    (set
      (mapcat
       (fn [new-source]
         (let [current-image (hyperfunction-set-image rel new-source)]
           (map
             (fn [i]
               (list new-source (union current-image i)))
             (power-set (difference out current-image)))))
       (power-set in)))))

; Hyperfunctions form a dagger category with a converse operation
(defn hyperfiber
  [rel target-element]

  (set
    (filter
      (fn [i]
        (contains? (rel i) target-element))
      (source-object rel))))

(defn converse-hyperfunction
  [rel]

  (Hyperfunction.
    (target-object rel)
    (source-object rel)
    (fn [target-element]
      (hyperfiber rel target-element))))

(defn converse-hyperfunction-set-image
  [rel coll]

  (apply
    union
    (map
      (fn [i]
        (hyperfiber rel i))
      coll)))

(defn converse-hyperfunction-set-inverse-image
  [hyperfunction source-set]

  (set
    (filter
      (fn [target-element]
        (superset? (list (hyperfiber hyperfunction target-element) source-set)))
      (target-object hyperfunction))))

; Images as established by multimethods
(defmethod image
  [Hyperfunction :locus.base.logic.core.set/universal]
  [func coll]

  (hyperfunction-set-image func coll))

(defmethod inverse-image
  [Hyperfunction :locus.base.logic.core.set/universal]
  [func coll]

  (hyperfunction-set-inverse-image func coll))

; Adjoin inputs and outputs to hyperfunctions
(defmethod adjoin-inputs Hyperfunction
  [rel coll]

  (Hyperfunction.
    (union coll (source-object rel))
    (target-object rel)
    (fn [i]
      (rel i))))

(defmethod adjoin-outputs Hyperfunction
  [rel coll]

  (Hyperfunction.
    (source-object rel)
    (union coll (target-object rel))
    (fn [i]
      (rel i))))

; Hyperfunctions have the property that every pair (X,Y) that is a subset of their inputs and their
; outputs can be used to create a subobject.
(defn subhyperfunction
  [rel new-in new-out]

  (Hyperfunction.
    new-in
    new-out
    (fn [i]
      (intersection new-out (rel i)))))

(defn restrict-hyperfunction
  [rel new-in]

  (Hyperfunction.
    new-in
    (target-object rel)
    (fn [i]
      (rel i))))

(defn restrict-hyperfunction-target
  [rel new-out]

  (subhyperfunction rel (source-object rel) new-out))

; Hyperfunction also have the property that every pair (P,Q) of partitions induces a quotient
; hyperfunction as congruences are simply ways of keeping things single-valued and that is not
; an issue here.
(defn quotient-hyperfunction
  [rel in-partition out-partition]

  (Hyperfunction.
    in-partition
    out-partition
    (fn [in-part]
      (let [outs (hyperfunction-set-image rel in-part)]
        (set
          (map
            (fn [out]
              (projection out-partition out))
            outs))))))

; Set relation triples
(defn hyperfunction-triple
  [rel]

  (list
    (source-object rel)
    (target-object rel)
    (underlying-relation rel)))

; Hom classes in Rel are partially ordered and complemented
(defn empty-hyperfunction
  [source target]

  (Hyperfunction.
    source
    target
    (fn [i]
      #{})))

(defn complete-hyperfunction
  [source target]

  (Hyperfunction.
    source
    target
    (fn [i]
      target)))

(defn complement-hyperfunction
  [rel]

  (let [in (source-object rel)
        out (target-object rel)]
    (Hyperfunction.
      in
      out
      (fn [i]
        (difference in (rel i))))))

; Singleton images hyperfunctions
(defn singleton-images-hyperfunction
  [^ImageFunction func]

  (->Hyperfunction
    (.-source func)
    (.-target func)
    (.-func func)))

; Conversion routines for set valued functions
(defn to-set-valued-function
  [hyperfunction]

  (SetFunction.
    (source-object hyperfunction)
    (->PowerSet (target-object hyperfunction))
    (fn [x]
      (hyperfunction x))))

(defn from-set-valued-function
  [func]

  (->Hyperfunction
    (inputs func)
    (dimembers (outputs func))
    (fn [i]
      (func i))))

; Products and coproducts of hyperfunctions
(defmethod product Hyperfunction
  [& relations]

  (Hyperfunction.
    (apply product (map source-object relations))
    (apply product (map target-object relations))
    (fn [coll]
      (apply
        product
        (map-indexed
          (fn [i v]
            ((nth relations i) v))
          coll)))))

(defmethod coproduct Hyperfunction
  [& relations]

  (Hyperfunction.
    (apply coproduct (map source-object relations))
    (apply coproduct (map target-object relations))
    (fn [[i v]]
      (set
        (map
          (fn [w]
            (list i w))
          ((nth relations i) v))))))

; The category Rel of sets and hyperfunctions is a locally ordered category, and so each Hom(a,b)
; of hyperfunctions between two sets is a poset, but not only is it a poset but it is a lattice
; as well. This allows us to compute the join and meet of hyperfunctions.
(defn included-hyperfunction?
  [a b]

  (and
    (superset? (list (source-object a) (source-object b)))
    (superset? (list (target-object a) (target-object b)))
    (every?
      (fn [i]
        (superset? (list (a i) (b i))))
      (source-object a))))

(defn join-hyperfunctions
  [& hyperfunctions]

  (let [func (first hyperfunctions)]
    (->Hyperfunction
      (source-object func)
      (target-object func)
      (fn [i]
        (apply
          union
          (map
            (fn [hyperfunction]
              (hyperfunction i))
            hyperfunctions))))))

(defn meet-hyperfunctions
  [& hyperfunctions]

  (let [func (first hyperfunctions)]
    (->Hyperfunction
     (source-object func)
     (target-object func)
     (fn [i]
       (apply
         intersection
         (map
           (fn [hyperfunction]
             (hyperfunction i))
           hyperfunctions))))))

(defn hyperhom
  [a b]

  (->Universal
    (fn [rel]
      (and
        (= (type rel) Hyperfunction)
        (equal-universals? a (source-object rel))
        (equal-universals? b (target-object rel))))))

; Ontology of morphisms in the allegory Rel of sets and hyperfunctions
(defmulti hyperfunction? type)

(defmethod hyperfunction? Hyperfunction
  [hyperfunction] true)

(defmethod hyperfunction? :default
  [obj] false)

; Special classes of hyperfunctions by rank
(defn ^{:private true} hyperfunction-is-of-rank?
  [rel rank]

  (every?
    (fn [i]
      (<= (count (rel i)) rank))
    (source-object rel)))

(defn functional-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (hyperfunction-is-of-rank? rel 1)))

(defn rank-two-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (hyperfunction-is-of-rank? rel 2)))

(defn rank-three-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (hyperfunction-is-of-rank? rel 3)))

(defn rank-four-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (hyperfunction-is-of-rank? rel 4)))

; Special classes of hyperfunctions
(defn reversible-functional-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (loop [coll (seq (source-object rel))
           outputs #{}]
      (if (empty? coll)
        true
        (let [next-input (first coll)
              current-outputs (rel next-input)]
          (and
            (= (count current-outputs) 1)
            (let [next-output (first current-outputs)]
              (and
                (not (contains? outputs next-output))
                (recur
                  (rest coll)
                  (conj outputs next-output))))))))))

(defn functional-hypertransformation?
  [rel]

  (and
    (functional-hypertransformation? rel)
    (= (source-object rel) (target-object rel))))

(defn reversible-functional-hypertransformation?
  [rel]

  (and
    (reversible-functional-hyperfunction? rel)
    (= (source-object rel) (target-object rel))))

(defn coreflexive-hypertransformation?
  [rel]

  (and
    (functional-hypertransformation? rel)
    (every?
      (fn [i]
        (or
          (= (rel i) #{})
          (= (rel i) #{i})))
      rel)))

(defn total-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (every?
      (fn [i]
        (not (empty? (rel i))))
      (source-object rel))))

(defn total-functional-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (every?
      (fn [i]
        (= (count (rel i)) 1))
      (source-object rel))))

(defn inverse-functional-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (every?
      (fn [i]
        (= (count (converse-hyperfunction-set-image rel #{i})) 1))
      (target-object rel))))

(defn hypertransformation?
  [rel]

  (and
    (hyperfunction? rel)
    (= (source-object rel) (target-object rel))))

(defn reflexive-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (every?
      (fn [i]
        (contains? (rel i) i))
      (source-object rel))))

(defn irreflexive-hyperfunction?
  [rel]

  (and
    (hyperfunction? rel)
    (every?
      (fn [i]
        (not (contains? (rel i) i)))
      (source-object rel))))

(defn reflexive-hypertransformation?
  [rel]

  (and
    (hypertransformation? rel)
    (reflexive-hyperfunction? rel)))

(defn irreflexive-hypertransformation?
  [rel]

  (and
    (hypertransformation? rel)
    (irreflexive-hyperfunction? rel)))

(defn symmetric-hyperfunction?
  [hyperfunction]

  (and
    (hyperfunction? hyperfunction)
    (let [rel (underlying-relation hyperfunction)]
      (every?
        (fn [pair]
          (contains? rel (reverse pair)))
        rel))))

(defn antisymmetric-hyperfunction?
  [hyperfunction]

  (and
    (hyperfunction? hyperfunction)
    (let [rel (underlying-relation hyperfunction)]
      (every?
        (fn [pair]
          (not (contains? rel (reverse pair))))
        rel))))
