(ns locus.elementary.incidence.system.family
  (:require [clojure.set]
            [locus.base.logic.core.set :refer :all])
  (:import [locus.base.logic.core.set Universal SeqableUniversal]))

; The basics of set theoretic ontology:
; A possible foundation of mathematics is in set theory. In this theory, everything
; is a set. Then building on the basic concept of a set, more complicated structures
; are constructed in set theory by the hierarchical nesting of sets. This leads to
; set systems which are sets of sets. In this file, we extensively develop the
; theory and ontology of set systems.

; We ultimately take topos theoretic foundations of mathematics. In this foundational
; framework all set theory is simply considered to be a part of the theory of the
; topos of Sets. All previous set theoretic work is still equally valid, it is just
; that our mathematical universe has been greatly opened up to new possiblities
; provided by other copresheaf topoi besides the topos of Sets.

; Family of universals classification
(defn family-of-universals?
  [coll]
  
  (and (universal? coll) (every? universal? coll)))

(defn cardinality-distinct-family?
  [family]

  (or
   (empty? family)
   (distinct? (map count family))))

; Families inclusion ordering
; The most general form of subfamilies is to check if the subfamily
; can be constructed by eliminating members and dimembers
(defn degree-reductions
  [family]

  (letfn [(product-of-finite-sets [& colls]
            (if (empty? colls)
              #{(list)}
              (set
               (mapcat
                (fn [i]
                  (map
                   #(cons i %)
                   (apply product-of-finite-sets (rest colls))))
                (first colls)))))]
    (set
     (map
      set
      (apply
       product-of-finite-sets
       (set
        (map
         power-set
         family)))))))

(defn nullfree-degree-reductions
  [family]

  (set
   (map
    (comp set (partial filter (complement empty?)))
    (degree-reductions family))))

(def inclusion-superfamily?
  (assoc (Universal.
          (intersection
            superset?
            (partial every? family-of-universals?)))
    :arities #{2}
    :query (fn [arg]
             (if (every? (partial every? family-of-universals?) arg)
               ((:query superset?) arg)
               #{}))))

(def superfamily?
  (letfn [(subfamilies [family]
            (apply
             union
             (map
              (fn [i]
                (if (contains? i #{})
                  #{i
                    (disj i #{})}
                  #{i}))
              (degree-reductions family))))
          (descendent-of? [[a b]]
            (contains? (subfamilies b) a))]
    (assoc (Universal. (intersection seq? descendent-of?))
      :arities #{2}
      :query (fn [arg]
               (case [(count (first arg)) (count (second arg))]
                 [1 0] (let [[[coll] []] arg]
                         (fn [i]
                           (descendent-of? i coll)))
                 [0 1] (let [[[] [coll]] arg]
                         (subfamilies coll))
                 #{})))))

; Subfamilies and subspaces
(defn subfamily
  "Generalized submembers"
  [family coll]

  (if (set? family)
    (set
     (filter
      (fn [elem]
        (superset? (list elem coll)))
      family))
    (set
     (filter
      family
      (power-set coll)))))

(defn subfamilies
  [pred? family]

  (set
   (filter
    (fn [coll]
      (pred? (subfamily family coll)))
    (power-set (apply union family)))))

(defn subspace
  "Restrict the members of the family"
  [family coll]

  (set
   (map
    (fn [i]
      (intersection i coll))
    family)))

(defn subspaces
  [pred? family]

  (set
   (filter
    (fn [coll]
      (pred? (subspace family coll)))
    (power-set (apply union family)))))

; Order theory
; The classification of set systems based upon their inclusion ordering.
; Related theories include the connected components, minimal members,
; maximal members, and lattice theoretic properties among others.
(defn order-connected-components
  [family]
  
  (letfn [(independent? [a b]
            (not (or (superset? (list a b))
                     (superset? (list b a)))))
          (get-new-dependents [unchecked-elems checked-elems]
            (set
             (filter
              (fn [unchecked-elem]
                (not
                 (every?
                  (fn [elem]
                    (independent? elem unchecked-elem))
                  checked-elems)))
              unchecked-elems)))
          (get-dependent-component [unchecked-elems checked-elems]
            (let [new-dependents (get-new-dependents unchecked-elems checked-elems)]
              (if (= (count new-dependents) 0)
                checked-elems
                (get-dependent-component
                 (difference unchecked-elems new-dependents)
                 (union checked-elems new-dependents)))))
          (get-dependent-components [coll]
            (if (= (count coll) 0)
              #{}
              (let [first-index (first coll)
                    current-component (get-dependent-component
                                       (difference coll #{first-index})
                                       #{first-index})]
                (union
                 #{current-component}
                 (get-dependent-components (difference coll current-component))))))]
    (get-dependent-components family)))

(defn maximum-order-component-size
  [family]

  (let [components (order-connected-components family)]
    (if (empty? components)
      0
      (apply max (map count components)))))

; Minimal and maximal members
(defn minimal-members
  [family]

  (set
   (filter
    (fn [elem]
      (every?
       (fn [coll]
         (or
           (= elem coll)
           (not (superset? (list coll elem)))))
       family))
    family))) 

(defn maximal-members
  [family]

  (set
   (filter
    (fn [elem]
      (every?
       (fn [coll]
         (or
           (= elem coll)
           (not (superset? (list elem coll)))))
       family))
    family)))

(defn isolated-members
  [family]

  (intersection (minimal-members family) (maximal-members family)))

(defn extremal-members
  [family]

  (union (minimal-members family) (maximal-members family)))

; Order related types of members
(defn submembers
  [family coll]

  (set
   (filter
    (fn [i]
      (superset? (list i coll)))
    family)))

(defn supermembers
  [family coll]

  (set
   (filter
    (fn [i]
      (superset? (list coll i)))
    family)))

(defn comparable-members
  [family coll]

  (set
   (filter
    (fn [i]
      (or (superset? (list coll i))
          (superset? (list i coll))))
    family)))

(defn incomparable-members
  [family coll]

  (set
   (filter
    (fn [i]
      (and (not (superset? (list coll i)))
           (not (superset? (list i coll)))))
    family)))

; Direct submembers and direct supermembers
(defn direct-submembers
  [family coll]

  (set
   (filter
    (fn [submember]
      (and
       (not= coll submember)
       (superset? (list submember coll))
       (every?
        (fn [middle]
          (not
            (and
              (not= middle coll)
              (not= middle submember)
              (superset? (list submember middle))
              (superset? (list middle coll)))))
        family)))
    family)))

(defn direct-supermembers
  [family coll]

  (set
   (filter
    (fn [supermember]
      (and
       (not= coll supermember)
       (superset? (list coll supermember))
       (every?
        (fn [middle]
          (not
            (and
              (not= middle coll)
              (not= middle supermember)
              (superset? (list coll middle))
              (superset? (list middle supermember)))))
        family)))
    family)))

(defn directly-comparable-members
  [family coll]
  
  (set
   (filter
    (fn [i]
      (and
       (or (superset? (list coll i))
           (superset? (list i coll)))
       (every?
        (fn [middle]
          (not
            (and
              (not= i coll)
              (not= middle coll)
              (not= middle i)
              (or
                (and
                  (superset? (list i middle))
                  (superset? (list middle coll)))
                (and
                  (superset? (list coll middle))
                  (superset? (list middle i)))))))
        family)))
    family)))

; Interval members
(defn interval-members
  [family child-coll parent-coll]

  (intersection
   (supermembers family child-coll)
   (submembers family parent-coll)))

; Comparability degree
(defn comparability-degree
  [family i]

  (count (comparable-members family i)))

(defn maximum-comparability-degree
  [family]

  (if (empty? family)
    0
    (apply max (map (partial comparability-degree family) family))))

(defn minimum-comparability-degree
  [family]

  (if (empty? family)
    0
    (apply min (map (partial comparability-degree family) family))))

; Suprema and infima
(defn upper-bound-members
  [family elems]

  (set
    (filter
     (fn [i]
       (every?
        (fn [elem]
          (superset? (list elem i)))
        elems))
     family)))

(defn lower-bound-members
  [family elems]

  (set
   (filter
    (fn [i]
      (every?
       (fn [elem]
         (superset? (list i elem)))
       elems))
    family)))

(defn suprema-members
  [family elems]
  
  (minimal-members (upper-bound-members family elems)))

(defn infima-members
  [family elems]

  (maximal-members (lower-bound-members family elems)))

(defn join-members
  [family elems]

  (if (empty? elems)
    (first (minimal-members family))
    (first (suprema-members family elems))))

(defn meet-members
  [family elems]

  (if (empty? elems)
    (first (maximal-members family))
    (first (infima-members family elems))))

; Family width and height
(defn family-width
  [family]

  (letfn [(contains-antichain-of-size? [family n]
            (not
             (every?
              (complement
               (fn [coll]
                 (every?
                  (fn [pair]
                    (not (contains? pair (apply intersection pair))))
                  (selections coll 2))))
              (selections family n))))
          (get-maximal-antichain-size [family current-n]
            (let [next-n (inc current-n)]
              (if (contains-antichain-of-size? family next-n)
                (get-maximal-antichain-size family next-n)
                current-n)))]
    (if (empty? family)
      0
      (get-maximal-antichain-size family 1))))

(defn family-height
  [family]

  (letfn [(contains-chain-of-size? [family n]
            (not
             (every?
              (complement
               (fn [coll]
                 (every?
                  (fn [pair]
                    (contains? pair (apply intersection pair)))
                  (selections coll 2))))
              (selections family n))))
          (get-maximal-chain-size [family current-n]
            (let [next-n (inc current-n)]
              (if (contains-chain-of-size? family next-n)
                (get-maximal-chain-size family next-n)
                current-n)))]
    (if (empty? family)
      0
      (get-maximal-chain-size family 1))))

; Classification of partial orders by forbidden suborders
(defn sperner-family?
  [coll]

  (every?
   (fn [pair]
     (not (contains? pair (apply intersection pair))))
   (selections coll 2)))

(defn chain-family?
  [family]

  (every?
   (fn [pair]
     (contains? pair (apply intersection pair)))
   (selections family 2)))

(def unique-family?
  (intersection
   family-of-universals?
   (cardinality-classification #{0 1})))

; Forbid partial orders of size at most three
(defn height-two-family?
  [family]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      (let [a (apply intersection pair)
            b (apply union pair)]
        (every?
         (fn [coll]
           (not
             (and
               (not= coll a)
               (not= coll b)
               (superset? (list a coll))
               (superset? (list coll b)))))
         family))))
   (selections family 2)))

(defn upper-forest-family?
  [family]

  (every?
   (fn [pair]
     (or
      (contains? pair (apply intersection pair))
      (every?
       (fn [i]
         (not
          (every?
           (fn [j]
             (superset? (list i j)))
           pair)))
       (difference family pair))))
   (selections family 2)))

(defn lower-forest-family?
  [family]

  (every?
   (fn [pair]
     (or
      (contains? pair (apply intersection pair))
      (every?
       (fn [i]
         (not
          (every?
           (fn [j]
             (superset? (list j i)))
           pair)))
       (difference family pair))))
   (selections family 2)))

(defn weak-ordered-family?
  [family]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      (let [a (apply intersection pair)
            b (apply union pair)]
        (every?
         (fn [i]
           (or
             (superset? (list a i))
             (superset? (list i b))))
         family))))
   (selections family 2)))

(defn width-two-family?
  [family]

  (every?
   (complement sperner-family?)
   (selections family 3)))

(defn multichain-family?
  [family]

  (every? chain-family? (order-connected-components family)))

(def height-two-upper-forest-family?
  (intersection
   height-two-family?
   upper-forest-family?))

(def height-two-lower-forest-family?
  (intersection
   height-two-family?
   lower-forest-family?))

(def weak-upper-forest-family?
  (intersection
   weak-ordered-family?
   upper-forest-family?))

(def weak-lower-forest-family?
  (intersection
   weak-ordered-family?
   lower-forest-family?))

(def height-two-weak-ordered-family?
  (intersection
   height-two-family?
   weak-ordered-family?))

(defn height-two-multichain-family?
  [family]

  (every?
   (fn [i]
     (<= (count i) 2))
   (order-connected-components family)))

(def weak-multichain-family?
  (intersection
   weak-ordered-family?
   multichain-family?))

(def height-two-weak-upper-forest-family?
  (intersection
   height-two-family?
   weak-ordered-family?
   upper-forest-family?))

(def height-two-weak-lower-forest-family?
  (intersection
   height-two-family?
   weak-ordered-family?
   lower-forest-family?))

(def height-two-weak-multichain-family?
  (intersection
   height-two-family?
   weak-ordered-family?
   multichain-family?))

(def width-two-upper-forest-family?
  (intersection
   width-two-family?
   upper-forest-family?))

(def width-two-lower-forest-family?
  (intersection
   width-two-family?
   lower-forest-family?))

(def width-two-multichain-family?
  (intersection
   width-two-family?
   multichain-family?))

(def width-two-weak-ordered-family?
  (intersection
   width-two-family?
   weak-ordered-family?))

(def width-two-weak-upper-forest-family?
  (intersection
   width-two-family?
   weak-ordered-family?
   upper-forest-family?))

(def width-two-weak-lower-forest-family?
  (intersection
   width-two-family?
   weak-ordered-family?
   lower-forest-family?))

(def width-two-weak-multichain-family?
  (intersection
   width-two-family?
   weak-ordered-family?
   multichain-family?))

(defn max-size-two-family?
  [family]

  (and
   (family-of-universals? family)
   (<= (count family) 2)))

(defn height-two-chain-family?
  [family]

  (or
   (<= (count family) 1)
   (and
    (= (count family) 2)
    (contains? family (apply intersection family)))))

(defn width-two-sperner-family?
  [family]

  (or
   (<= (count family) 1)
   (and
    (= (count family) 2)
    (not (contains? family (apply intersection family))))))

; Forbid partial orders of size at most four
(defn height-three-family?
  [family]

  (<= (family-height family) 3))

(defn lower-common-point-free?
  "Lower common point free families forbid [2 1 1]"
  [family]

  (every?
   (fn [coll]
     (not
      (and
       (= (count (minimal-members coll)) 2)
       (= (count (maximal-members coll)) 1)
       (weak-ordered-family? coll))))
   (selections family 4)))

(defn upper-common-point-free?
  "Upper common point free families forbid [1 1 2]"
  [family]

  (every?
   (fn [coll]
     (not
      (and
       (= (count (minimal-members coll)) 1)
       (= (count (maximal-members coll)) 2)
       (weak-ordered-family? coll))))
   (selections family 4)))

(defn diamond-free-ordered-family?
  "Diamond free families forbid [1 2 1]"
  [family]

  (every?
   (fn [coll]
     (not
      (and
       (= (count (minimal-members coll)) 1)
       (= (count (maximal-members coll)) 1)
       (weak-ordered-family? coll)
       (not (chain-family? coll)))))
   (selections family 4)))

(defn weak-parts-family?
  [family]

  (every?
   (fn [i]
     (let [current-parts (set
                          (filter
                           (fn [j]
                             (superset? (list j i)))
                           (disj family i)))]
       (weak-ordered-family? current-parts)))
   family))

(defn weak-parents-family?
  [family]

  (every?
   (fn [i]
     (let [current-parents (set
                            (filter
                             (fn [j]
                               (superset? (list i j)))
                             (disj family i)))]
       (weak-ordered-family? current-parents)))
   family))

(defn strongly-unique-extrema-family?
  [family]

  (every?
   (fn [coll]
     (every?
      (fn [pair]
        (let [remaining-elems (difference coll pair)]
          (not
            (and
              (not (contains? pair (apply intersection pair)))
              (not (contains? remaining-elems (apply intersection remaining-elems)))
              (let [[a b] (seq pair)
                  [c d] (seq remaining-elems)]
                (and
                  (superset? (list a c))
                  (superset? (list a d))
                  (superset? (list b c))
                  (superset? (list b d))))))))
      (selections coll 2)))
   (selections family 4)))

(defn width-two-parts-family?
  [family]

  (every?
   (fn [i]
     (let [current-parts (set
                          (filter
                           (fn [j]
                             (superset? (list j i)))
                           (disj family i)))]
       (width-two-family? current-parts)))
   family))

(defn width-two-parents-family?
  [family]

  (every?
   (fn [i]
     (let [current-parents (set
                            (filter
                             (fn [j]
                               (superset? (list i j)))
                             (disj family i)))]
       (width-two-family? current-parents)))
   family))

(defn series-parallel-family?
  [family]

  (every?
   (fn [coll]
     (not
      (and
       (unique-family? (order-connected-components coll))
       (= (count (minimal-members coll)) (count (maximal-members coll)) 2)
       (not (weak-ordered-family? coll)))))
   (selections family 4)))

(defn colocally-height-two-family?
  [family]

  (every?
   (fn [i]
     (let [incomparable-elements (set
                                  (filter
                                   (fn [j]
                                     (not
                                       (or
                                         (superset? (list i j))
                                         (superset? (list j i)))))
                                   family))]
       (height-two-family? incomparable-elements)))
   family))

(defn interval-ordered-family?
  [family]

  (every?
   (fn [coll]
     (let [connected-components (order-connected-components coll)]
       (not
        (and
         (= (count connected-components) 2)
         (every? (fn [i] (= (count i) 2)) connected-components)))))
   (selections family 4)))

(defn upper-forest-coneighbourhood-family?
  [family]

  (every?
   (fn [i]
     (let [incomparable-elements (set
                                  (filter
                                   (fn [j]
                                     (not
                                       (or
                                         (superset? (list i j))
                                         (superset? (list j i)))))
                                   family))]
       (upper-forest-family? incomparable-elements)))
   family))

(defn lower-forest-coneighbourhood-family?
  [family]

  (every?
   (fn [i]
     (let [incomparable-elements (set
                                  (filter
                                   (fn [j]
                                     (not
                                       (or
                                         (superset? (list i j))
                                         (superset? (list j i)))))
                                   family))]
       (lower-forest-family? incomparable-elements)))
   family))

(defn colocally-weak-family?
  [family]

  (every?
   (fn [i]
     (let [incomparable-elements (set
                                  (filter
                                   (fn [j]
                                     (not
                                       (or
                                         (superset? (list i j))
                                         (superset? (list j i)))))
                                   family))]
       (weak-ordered-family? incomparable-elements)))
   family))

(defn width-three-family?
  [family]

  (every? (complement sperner-family?) (selections family 4)))

(def multichain-parts-family?
  (intersection
   lower-common-point-free?
   diamond-free-ordered-family?))

(def multichain-parents-family?
  (intersection
   upper-common-point-free?
   diamond-free-ordered-family?))

(def semicommon-point-free?
  (intersection
   lower-common-point-free?
   upper-common-point-free?))

(def locally-weak-family?
  (intersection
   weak-parts-family?
   weak-parents-family?))

(def locally-width-two-family?
  (intersection
   width-two-parts-family?
   width-two-parents-family?))

(def arborescence-family?
  (intersection
   series-parallel-family?
   strongly-unique-extrema-family?))

(def series-parallel-interval-ordered-family?
  (intersection
   series-parallel-family?
   interval-ordered-family?))

(def split-ordered-family?
  (intersection
   strongly-unique-extrema-family?
   interval-ordered-family?))

(def semiordered-family?
  (intersection
   colocally-height-two-family?
   interval-ordered-family?))

(defn colocally-multichain-family?
  [family]

  (every?
   (fn [i]
     (let [incomparable-elements (set
                                  (filter
                                   (fn [j]
                                     (not
                                       (or
                                         (superset? (list i j))
                                         (superset? (list j i)))))
                                   family))]
       (multichain-family? incomparable-elements)))
   family))

(def locally-multichain-family?
  (intersection
   diamond-free-ordered-family?
   lower-common-point-free?
   upper-common-point-free?))

(def multiweak-family?
  (intersection
   locally-weak-family?
   series-parallel-family?))

(def forest-ordered-family?
  (intersection
   diamond-free-ordered-family?
   strongly-unique-extrema-family?
   series-parallel-family?))

(def multiweak-arborescence-family?
  (intersection
   locally-weak-family?
   series-parallel-family?
   strongly-unique-extrema-family?))

(def series-parallel-semiordered-family?
  (intersection
   series-parallel-family?
   semiordered-family?))

(def split-semiordered-family?
  (intersection
   strongly-unique-extrema-family?
   semiordered-family?))

(def threshold-ordered-family?
  (intersection
   strongly-unique-extrema-family?
   series-parallel-family?
   interval-ordered-family?))

(def locally-width-two-weak-family?
  (intersection
   width-two-parts-family?
   width-two-parents-family?
   weak-parts-family?
   weak-parents-family?))

(def threshold-semiordered-family?
  (intersection
   strongly-unique-extrema-family?
   series-parallel-family?
   semiordered-family?))

(def locally-width-two-multichain-family?
  (intersection
   width-two-parts-family?
   width-two-parents-family?
   diamond-free-ordered-family?
   lower-common-point-free?
   upper-common-point-free?))

(def locally-weak-multichain-family?
  (intersection
   weak-parts-family?
   weak-parents-family?
   diamond-free-ordered-family?
   lower-common-point-free?
   upper-common-point-free?))

(def locally-multichain-forest-ordered-family?
  (intersection
   upper-common-point-free?
   lower-common-point-free?
   diamond-free-ordered-family?
   strongly-unique-extrema-family?
   series-parallel-family?))

(def multiweak-forest-ordered-family?
  (intersection
   weak-parts-family?
   weak-parents-family?
   diamond-free-ordered-family?
   series-parallel-family?
   strongly-unique-extrema-family?))

(def locally-weak-multichain-forest-ordered-family?
  (intersection
   locally-weak-multichain-family?
   forest-ordered-family?))

(def locally-width-two-weak-multichain-family?
  (intersection
   locally-width-two-family?
   locally-weak-family?
   locally-multichain-family?))

(defn bilocal-family?
  [family]

  (every?
   (fn [elem]
     (let [comparators (set
                        (filter
                         (fn [i]
                           (or (superset? (list i elem))
                               (superset? (list elem i))))
                         (disj family elem)))]
       (<= (count comparators) 2)))
   family))

(def bilocal-forest-ordered-family?
  (intersection
   bilocal-family?
   forest-ordered-family?))

(defn max-size-three-family?
  [family]

  (and
   (family-of-universals? family)
   (<= (count family) 3)))

(def height-two-strongly-unique-extrema-family?
  (intersection
   height-two-family?
   strongly-unique-extrema-family?))

(def height-two-forest-ordered-family?
  (intersection
   height-two-family?
   series-parallel-family?
   strongly-unique-extrema-family?))

(def upper-dependency-ordered-family?
  (intersection
   height-two-family?
   strongly-unique-extrema-family?
   width-two-parents-family?))

(def lower-dependency-ordered-family?
  (intersection
   height-two-family?
   strongly-unique-extrema-family?
   width-two-parts-family?))

(def bidependency-ordered-family?
  (intersection
   height-two-family?
   strongly-unique-extrema-family?
   locally-width-two-family?))

(def height-two-multiweak-family?
  (intersection
   height-two-family?
   series-parallel-family?))

(def height-two-bilocal-family?
  (intersection
   height-two-family?
   bilocal-family?))

(def height-two-bilocal-multiweak-family?
  (intersection
   height-two-family?
   bilocal-family?
   multiweak-family?))

(def height-two-bilocal-forest-ordered-family?
  (intersection
   height-two-family?
   bilocal-forest-ordered-family?))

(def height-two-bilocal-upper-forest-family?
  (intersection
   height-two-upper-forest-family?
   bilocal-family?))

(def height-two-bilocal-lower-forest-family?
  (intersection
   height-two-lower-forest-family?
   bilocal-family?))

(def multiweak-upper-forest-family?
  (intersection
   multiweak-family?
   upper-forest-family?))

(def multiweak-lower-forest-family?
  (intersection
   multiweak-family?
   lower-forest-family?))

(def locally-multichain-upper-forest-family?
  (intersection
   lower-common-point-free?
   upper-forest-family?))

(def locally-multichain-lower-forest-family?
  (intersection
   upper-common-point-free?
   lower-forest-family?))

(def locally-weak-multichain-upper-forest-family?
  (intersection
   locally-weak-multichain-family?
   upper-forest-family?))

(def locally-weak-multichain-lower-forest-family?
  (intersection
   locally-weak-multichain-family?
   lower-forest-family?))

(def weak-arborescence-family?
  (intersection
   weak-ordered-family?
   strongly-unique-extrema-family?))

(def weak-forest-ordered-family?
  (intersection
   weak-ordered-family?
   strongly-unique-extrema-family?
   diamond-free-ordered-family?))

(def height-two-weak-forest-ordered-family?
  (intersection
   weak-ordered-family?
   height-two-family?
   strongly-unique-extrema-family?))

; Forbid partial orders of size at most five
(defn height-four-family?
  [family]

  (<= (family-height family) 4))

(defn common-point-free?
  "Common point free families forbid [2 1 2]"
  [family]

  (every?
   (fn [i]
     (let [pairs (selections (disj family i) 2)
           incomparable-pairs (set
                               (filter
                                (fn [pair]
                                  (not (contains? pair (apply intersection pair))))
                                pairs))]
       (not
        (and
         (not
          (every?
           (complement
             (fn [pair]
              (every? (fn [elem] (superset? (list elem i))) pair)))
           incomparable-pairs))
         (not
          (every?
           (complement
             (fn [pair]
              (every? (fn [elem] (superset? (list i elem))) pair)))
           incomparable-pairs))))))
   family))

(defn width-four-family?
  [family]

  (every? (complement sperner-family?) (selections family 5)))

(defn max-size-four-family?
  [family]

  (and
   (family-of-universals? family)
   (<= (count family) 4)))

; Cardinality restricted families
(def singular-family?
  (intersection
   family-of-universals?
   singular-universal?))

(def size-two-family?
  (intersection
   family-of-universals?
   size-two-universal?))

(def size-three-family?
  (intersection
   family-of-universals?
   size-three-universal?))

(def size-four-family?
  (intersection
   family-of-universals?
   size-four-universal?))

; Uniquely connected families
(defn uniquely-connected-family?
  [family]

  (<= (count (order-connected-components family)) 1))

(defn unique-minima-family?
  [family]

  (<= (count (minimal-members family)) 1))

(defn unique-maxima-family?
  [family]

  (<= (count (maximal-members family)) 1))

(def uniquely-bounded-family?
  (intersection
   unique-minima-family?
   unique-maxima-family?))

; Specific uniquely connected families
(def uniquely-connected-height-two-family?
  (intersection
   uniquely-connected-family?
   height-two-family?))

(def uniquely-connected-strongly-unique-extrema-family?
  (intersection
   uniquely-connected-family?
   strongly-unique-extrema-family?))

; Tree dependency families
(def tree-ordered-family?
  (intersection
   uniquely-connected-family?
   forest-ordered-family?))

(def upper-tree-family?
  (intersection
   unique-maxima-family?
   upper-forest-family?))

(def lower-tree-family?
  (intersection
   unique-minima-family?
   lower-forest-family?))

(def height-two-tree-ordered-family?
  (intersection
   uniquely-connected-family?
   height-two-family?
   forest-ordered-family?))

(def height-two-lower-tree-family?
  (intersection
   unique-minima-family?
   height-two-lower-forest-family?))

(def height-two-upper-tree-family?
  (intersection
   unique-maxima-family?
   height-two-upper-forest-family?))

; Bilocal families
(def uniquely-connected-bilocal-family?
  (intersection
   uniquely-connected-family?
   bilocal-family?))

(defn crown-ordered-family?
  [family]

  (and
   (uniquely-connected-family? family)
   (every?
    (fn [i]
      (= (count (comparable-members family i)) 3))
    family)))

(defn fence-ordered-family?
  [family]

  (and
   (uniquely-connected-family? family)
   (bilocal-family? family)
   (not (crown-ordered-family? family))))

(defn multifence-ordered-family?
  [family]

  (every?
   fence-ordered-family?
   (order-connected-components family)))

; Forbidding bilocal families
(defn crown-free-ordered-family?
  [family]

  (let [possible-cardinalities (intersection
                                even?
                                (set (range 4 (inc (count family)))))]
    (every?
     (fn [new-elems]
       (not (crown-ordered-family? new-elems)))
     (multiselection family possible-cardinalities))))

(def block-ordered-family?
  (intersection
   crown-free-ordered-family?
   locally-multichain-family?))

(def height-two-block-ordered-family?
  (intersection
   height-two-family?
   block-ordered-family?))

; Unlatticeness
(defn dedekind-cuts
  [family]

  (set
   (filter
    (fn [i]
      (= i (lower-bound-members family (upper-bound-members family i))))
    (power-set family))))

(defn unlatticeness
  [family]

  (- (count (dedekind-cuts family)) (count family)))

; Unique extrema families
(defn unique-extrema-family?
  [family]

  (every?
   (fn [i]
     (and
      (<= (count (suprema-members family i)) 1)
      (<= (count (infima-members family i)) 1)))
   (selections family 2)))

(def uniquely-connected-unique-extrema-family?
  (intersection
   unique-extrema-family?
   uniquely-connected-family?))

(def join-semilattice-ordered-family?
  (intersection
   unique-maxima-family?
   unique-extrema-family?))

(def meet-semilattice-ordered-family?
  (intersection
   unique-minima-family?
   unique-extrema-family?))

(def lattice-ordered-family?
  (intersection
   uniquely-bounded-family?
   unique-extrema-family?))

; Join irreducibles
(defn suprema-irreducible-members
  [family]

  (difference
   (set
    (filter
     (fn [i]
       (not (<= 2 (count (direct-submembers family i)))))
     family))
   (let [minima (minimal-members family)]
     (if (= (count minima) 1)
       #{(first minima)}
       #{}))))

(defn join-irreducible-members
  [family]

  (difference
   (set
    (filter
     (fn [i]
       (not
        (and
         (<= 2 (count (direct-submembers family i)))
         (= (count (suprema-members family (direct-submembers family i))) 1))))
     family))
   (let [minima (minimal-members family)]
     (if (= (count minima) 1)
       #{(first minima)}
       #{}))))

(defn atomic-members
  [family]

  (minimal-members (join-irreducible-members family)))

(defn atomistic-ordered-family?
  [family]

  (sperner-family? (suprema-irreducible-members family)))

(defn multiatomistic-ordered-family?
  [family]
  
  (multichain-family? (suprema-irreducible-members family)))

(defn atomistic-lattice-ordered-family?
  [family]

  (and
   (lattice-ordered-family? family)
   (sperner-family? (join-irreducible-members family))))

(defn multiatomistic-lattice-ordered-family?
  [family]

  (and
   (lattice-ordered-family? family)
   (multichain-family? (join-irreducible-members family))))

; Multiset theory
; Multiset theory directly emerges from the understanding of the degrees
; of the set system. The degree of each member in a set system is the
; number of times that occurs in members of the set system.
(defn cardinality-sum
  [family]

  (apply + (map count family)))

(defn family-order
  [family]

  (count (apply union family)))

(defn minimum-degree
  [family]

  (let [dimembers (apply union family)]
    (if (empty? dimembers)
      0
      (apply min (map (partial degree family) dimembers)))))

(defn maximum-degree
  [family]

  (let [dimembers (apply union family)]
    (if (empty? dimembers)
      0
      (apply max (map (partial degree family) dimembers)))))

; Max cardinality sum
(defn max-cardinality-sum-three-family?
  [family]

  (<= (cardinality-sum family) 3))

(defn max-cardinality-sum-four-family?
  [family]

  (<= (cardinality-sum family) 4))

; Family order numbers
(defn rank-one-chain-family?
  [family]

  (<= (count (apply union family)) 1))

(defn max-order-two-family?
  [family]

  (<= (count (apply union family)) 2))

(defn max-order-three-family?
  [family]

  (<= (count (apply union family)) 3))

(defn max-order-four-family?
  [family]

  (<= (count (apply union family)) 4))

(defn order-one-family?
  [family]

  (= (count (apply union family)) 1))

(defn order-two-family?
  [family]

  (= (count (apply union family)) 2))

(defn order-three-family?
  [family]

  (= (count (apply union family)) 3))

(defn order-four-family?
  [family]

  (= (count (apply union family)) 4))

; Regular families
(defn regular-family?
  [family]

  (let [degree-sequence (map (partial degree family)
                             (apply union family))]
    (or (empty? degree-sequence) (apply = degree-sequence))))

; Independent families and maximum degrees
(defn independent-family?
  [coll]

  (every?
   (fn [pair]
     (<= (count (apply intersection pair)) 0))
   (selections coll 2)))

(defn maximum-degree-two-family?
  [family]

  (every?
   (fn [i]
     (<= (degree family i) 2))
   (apply union family)))

(defn maximum-degree-three-family?
  [family]

  (every?
   (fn [i]
     (<= (degree family i) 3))
   (apply union family)))

(defn maximum-degree-four-family?
  [family]

  (every?
   (fn [i]
     (<= (degree family i) 4))
   (apply union family)))

; Special classes of regular families
(defn two-regular-family?
  [family]

  (and
    (family-of-universals? family)
    (every?
      (fn [i]
        (= (degree family i) 2))
      (apply union family))))

(defn three-regular-family?
  [family]

  (and
    (family-of-universals? family)
    (every?
      (fn [i]
        (= (degree family i) 3))
      (apply union family))))

(defn four-regular-family?
  [family]

  (and
    (family-of-universals? family)
    (every?
      (fn [i]
        (= (degree family i) 4)
      (apply union family)))))

; Independent families of special sizes
(def max-order-two-independent-family?
  (intersection
   max-order-two-family?
   independent-family?))

(def max-order-three-independent-family?
  (intersection
   max-order-three-family?
   independent-family?))

(def max-order-four-independent-family?
  (intersection
   max-order-four-family?
   independent-family?))

(defn singular-unary-family?
  [family]

  (and
   (= (count family) 1)
   (= (count (apply union family)) 1)))

(def order-two-independent-family?
  (intersection
   order-two-family?
   independent-family?))

(def order-three-independent-family?
  (intersection
   order-three-family?
   independent-family?))

(def order-four-independent-family?
  (intersection
   order-four-family?
   independent-family?))

; Pseudo independent families
(defn total-intersection-size
  [family]

  (apply
   +
   (map
    (fn [pair]
      (count (apply intersection pair)))
    (selections family 2))))

(defn combinational-repetitiveness
  "Repetitiveness of the degrees multiset."
  [family]

  (repetitiveness (degrees family)))

(defn near-independent-family?
  [family]

  (<= (total-intersection-size family) 1))

; Powerful family
(defn powerful-family?
  [family]

  (every?
   (fn [i]
     (<= 2 (degree family i)))
   (apply union family)))

; Power families
(defn rank
  [family]

  (if (empty? family)
    0
    (apply max (map count family))))

(defn corank
  [family]

  (if (empty? family)
    Double/POSITIVE_INFINITY
    (apply min (map count family))))

(def nullfree-family?
  (power-set (intersection universal? (complement (cardinality-classification #{0})))))

(def corank-two-family?
  (power-set (intersection universal? (complement (cardinality-classification #{0 1})))))

(def corank-three-family?
  (power-set (intersection universal? (complement (cardinality-classification #{0 1 2})))))

(def corank-four-family?
  (power-set (intersection universal? (complement (cardinality-classification #{0 1 2 3})))))

(def singleton-free-family?
  (power-set (intersection universal? (complement (cardinality-classification #{1})))))

(def singleton-free-rank-two-family?
  (power-set (cardinality-classification #{0 2})))

(def rank-one-family?
  (power-set (cardinality-classification #{0 1})))

(def unary-family?
  (power-set (cardinality-classification #{1})))

(def rank-two-family?
  (power-set (cardinality-classification #{0 1 2})))

(def nullfree-rank-two-family?
  (power-set (cardinality-classification #{1 2})))

(def binary-family?
  (power-set (cardinality-classification #{2})))

(def rank-three-family?
  (power-set (cardinality-classification #{0 1 2 3})))

(def nullfree-rank-three-family?
  (power-set (cardinality-classification #{1 2 3})))

(def corank-two-rank-three-family?
  (power-set (cardinality-classification #{2 3})))

(def ternary-family?
  (power-set (cardinality-classification #{3})))

(def rank-four-family?
  (power-set (cardinality-classification #{0 1 2 3 4})))

(def nullfree-rank-four-family?
  (power-set (cardinality-classification #{1 2 3 4})))

(def corank-two-rank-four-family?
  (power-set (cardinality-classification #{2 3 4})))

(def corank-three-rank-four-family?
  (power-set (cardinality-classification #{3 4})))

(def quaternary-family?
  (power-set (cardinality-classification #{4})))

; Forbbiden subchains
(defn subnull-free?
  [family]

  (or
   (= family #{#{}})
   (not (contains? family #{}))))

(defn subnonnull-free?
  [coll]

  (every?
   (fn [pair]
     (not (contains? pair (apply intersection pair))))
   (selections (disj coll #{}) 2)))

(defn subsingleton-free?
  [family]

  (every?
   (fn [coll]
     (or
      (<= (count coll) 1)
      (every?
       (fn [i]
         (not
          (contains? family #{i})))
       coll)))
   family))

(defn subnonsingleton-free?
  [coll]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      (singular-universal? (apply intersection pair))))
   (selections coll 2)))

(def subunique-free?
  (intersection
   subnull-free?
   subsingleton-free?))

(defn subnonunique-free?
  [coll]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      ((cardinality-classification #{0 1}) (apply intersection pair))))
   (selections coll 2)))

(def singleton-isolated-family?
  (intersection
   subsingleton-free?
   (union
    (power-set (intersection universal? (complement (cardinality-classification #{0}))))
    (power-set (intersection universal? (complement (cardinality-classification #{1})))))))

(defn strongly-saturated-family?
  [family]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      (= 1 (- (count (apply union pair))
              (count (apply intersection pair))))))
   (selections family 2)))

(defn strongly-antisaturated-family?
  [family]

  (every?
   (fn [pair]
     (or
      (not (contains? pair (apply intersection pair)))
      (not= 1 (- (count (apply union pair))
                 (count (apply intersection pair))))))
   (selections family 2)))

; Forbidden sperner families
(defn laminar-family?
  [family]

  (every?
   (fn [pair]
     (or
      (contains? pair (apply intersection pair))
      (empty? (apply intersection pair))))
   (selections family 2)))

(def nullfree-laminar-family?
  (intersection
   nullfree-family?
   laminar-family?))

; Intersection multigraph
; Properties determined by the multiplicity of the intersection
; of component sets of the set system including the intersection
; graph as well as the higher multiplicities
(defn adjacency-connected-components
     [family]

     (letfn [(independent? [a b]
               (empty? (intersection a b)))
             (get-new-dependents [unchecked-elems checked-elems]
               (set
                (filter
                 (fn [unchecked-elem]
                   (not
                    (every?
                     (fn [elem]
                       (independent? elem unchecked-elem))
                     checked-elems)))
                 unchecked-elems)))
             (get-dependent-component [unchecked-elems checked-elems]
               (let [new-dependents (get-new-dependents unchecked-elems checked-elems)]
                 (if (empty? new-dependents)
                   checked-elems
                   (get-dependent-component
                    (difference unchecked-elems new-dependents)
                    (union checked-elems new-dependents)))))
             (get-dependent-components [coll]
               (if (empty? coll)
                 #{}
                 (let [first-index (first coll)
                       current-component (get-dependent-component
                                          (difference coll #{first-index})
                                          #{first-index})]
                   (union
                    #{current-component}
                    (get-dependent-components (difference coll current-component))))))]
       (get-dependent-components family)))

(defn intersecting-members
  [family coll]

  (set
   (filter
    (fn [i]
      (not (empty? (intersection coll i))))
    family)))

(defn intersection-count
  [a b]

  (count (intersection a b)))

(defn antidisjoint-family?
  [family]

  (every?
   (fn [pair]
     (not (empty? (apply intersection pair))))
   (selections family 2)))

(defn uniquely-dependent-family?
  [family]

  (<= (count (adjacency-connected-components family)) 1))

(defn intersection-cluster-family?
  [family]

  (every? antidisjoint-family? (adjacency-connected-components family)))

; Intersection numbers
(defn maximum-intersection-size
  [coll]

  (if (<= (count coll) 1)
    0
    (apply
     max
     (map
      (fn [pair]
        (count (apply intersection pair)))
      (selections coll 2)))))

(defn minimum-intersection-size
  [family]

  (if (<= (count family) 1)
    Double/POSITIVE_INFINITY
    (apply
     min
     (map
      (fn [i]
        (count (apply intersection i)))
      (selections family 2)))))

(defn linear-family?
  [family]

  (every?
   (fn [pair]
     (<= (count (apply intersection pair)) 1))
   (selections family 2)))

(defn antilinear-family?
  [family]

  (every?
   (fn [pair]
     (<= 2 (count (apply intersection pair))))
   (selections family 2)))

; Triplewise disjointness
(defn triplewise-disjoint-family?
  [family]

  (every?
   (fn [i]
     (empty? (apply intersection i)))
   (selections family 3)))

(defn quadruplewise-disjoint-family?
  [family]

  (every?
   (fn [i]
     (empty? (apply intersection i)))
   (selections family 4)))

; Adjacency graph
; Properties determined by the adjacency of dimembers of the 
; set system which is defined by the existence of some
; set which contains both of the adjacent dimembers
(defn adjacency-degree
  [family elem]

  (count (apply union (set (filter (fn [i] (contains? i elem)) family)))))

(defn minimum-adjacency-degree
  [family]

  (let [dimembers (apply union family)]
    (if (empty? dimembers)
      0
      (apply min (map (partial adjacency-degree family) dimembers)))))

(defn maximum-adjacency-degree
  [family]

  (let [dimembers (apply union family)]
    (if (empty? dimembers)
      0
      (apply max (map (partial adjacency-degree family) dimembers)))))

(defn adjacency-regular-family?
  [family]

  (let [degree-sequence (map (partial adjacency-degree family)
                             (apply union family))]
    (or (empty? degree-sequence) (apply = degree-sequence))))

; Family connectivity and the connectivity number
(defn family-connectivity
  [family]

  (set
   (for [component (adjacency-connected-components family)
         :when (not (every? empty? component))]
     (apply union component))))

(defn maximum-adjacency-component-size
  [family]

  (let [components (family-connectivity family)]
    (if (empty? components)
      0
      (apply max (map count components)))))

; Independence number
(defn independence-number
  [family]

  (rank (subfamilies rank-one-family? family)))
	
; Clique number
(defn maximal-cliques
  [family]

  (maximal-members
   (if (empty? family)
     #{}
     (let [underlying-coll (apply union family)
           unordered-tuples (intersection size-two-universal? (apply union (map power-set (maximal-members family))))]
       (set
        (filter
         (fn [coll]
           (superset? (list (selections coll 2) unordered-tuples)))
         (power-set underlying-coll)))))))

(def clique-number
  (comp rank maximal-cliques))

(defn triangle-free-family?
  [family]

  (<= (clique-number family) 2))

; Chromatic number
(defn chromatic-number
  [family]

  (letfn [(enumerate-set-partitions [coll n]
            (if (= n 1)
              #{#{coll}}
              (let [possible-sizes (range 1 (+ (- (count coll) n) 2))]
                (apply
                 union
                 (map
                  (fn [current-coll]
                    (set
                     (map
                      (fn [i]
                        (union i #{current-coll}))
                      (enumerate-set-partitions
                       (difference coll current-coll)
                       (dec n)))))
                  (multiselection coll (set possible-sizes)))))))
          (contains-coloring? [family partitions]
            (not
             (every?
              (complement
               (fn [partition]
                 (every?
                  (fn [coll]
                    (rank-one-family? (subfamily family coll)))
                  partition)))
              partitions)))
          (minimum-coloring-size [family n]
            (if (contains-coloring?
                 family
                 (enumerate-set-partitions (apply union family) n))
              n
              (minimum-coloring-size family (inc n))))]
    (let [minimum-size (clique-number family)
          maximum-size (count (apply union family))]
      (if (or (<= minimum-size 1)
              (= minimum-size maximum-size))
        minimum-size
        (minimum-coloring-size family minimum-size)))))

(defn family-coloring?
  [family partition]

  (every?
   (fn [part]
     (rank-one-family? (subfamily family part)))
   partition))

(defn bipartite-family?
  [family]

  (<= (chromatic-number family) 2))

; Helly numbers
(defn empty-intersection-family?
  [family]

  (and
   (not (empty? family))
   (empty? (apply intersection family))))

(defn minimally-independent-family?
  [family]

  (and
   (empty-intersection-family? family)
   (every?
    (fn [i]
      (not (empty-intersection-family? (disj family i))))
    family)))

(defn helly-number
  "Maximum minimally independent set size"
  [family]

  (let [counts
        (map
         count
         (filter
          minimally-independent-family?
          (power-set family)))]
    (if (empty? counts)
      0
      (apply max counts))))

(defn helly-family?
  "The helly number is less then or equal to two"
  [family]

  (every?
   (fn [coll]
     (or
      (<= (count coll) 2)
      (not (antidisjoint-family? coll))
      (not (empty? (apply intersection coll)))))
   (power-set family)))

; Dimembers
(defn neighbourhood
  "Singletonization parent members"
  [family i]

  (supermembers family #{i}))

(defn adjacencies
  [family i]

  (apply union (neighbourhood family i)))

(defn subdimembers
  [family i]

  (apply intersection (neighbourhood family i)))

(defn superdimembers
  [family i]

  (set
   (filter
    (fn [elem]
      (contains? (subdimembers family elem) i))
    (apply union family))))

(defn comparable-dimembers
  [family i]

  (union (superdimembers family i) (subdimembers family i)))

; Direct subdimembers
(defn direct-subdimembers
  [family i]

  (let [proper-subdimembers (disj (subdimembers family i) i)]
    (set
     (filter
      (fn [subdimember]
        (every?
         (fn [middle]
           (not
            (contains? (subdimembers family middle) subdimember)))
         (disj proper-subdimembers subdimember)))
      proper-subdimembers))))

(defn direct-superdimembers
  [family i]

  (let [proper-superdimembers (disj (superdimembers family i) i)]
    (set
     (filter
      (fn [superdimember]
        (every?
         (fn [middle]
           (not
            (contains? (superdimembers family middle) superdimember)))
         (disj proper-superdimembers superdimember)))
      proper-superdimembers))))

(defn directly-comparable-dimembers
  [family i]

  (union
   #{i}
   (direct-subdimembers family i)
   (direct-superdimembers family i)))

; Get elements with unique direct subdimembers
(defn lower-cover-singular-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (let [coll (direct-subdimembers family i)]
        (= (count coll) 1)))
    (apply union family))))

(defn upper-cover-singular-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (let [coll (direct-superdimembers family i)]
        (= (count coll) 1)))
    (apply union family))))

(defn lower-cover-unique-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (let [coll (direct-subdimembers family i)]
        (<= (count coll) 1)))
    (apply union family))))

(defn upper-cover-unique-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (let [coll (direct-superdimembers family i)]
        (<= (count coll) 1)))
    (apply union family))))

(defn multiple-dimembers
  [family]

  (let [elems (lower-cover-singular-dimembers family)]
    (set
     (filter
      (fn [i]
        (let [child (first (direct-subdimembers family i))]
          (= 1 (count (intersection
                       (direct-superdimembers family child)
                       elems)))))
      elems))))

; Distinguishability
(defn distinguishability
  "The distinguishability of dimembers by neighbourhoods"
  [family]

  (family-connectivity
   (set
    (filter
     (fn [coll]
       (apply = (map (partial neighbourhood family) coll)))
     (multiselection (apply union family) #{1 2})))))

(defn adjacency-distinguishability
  "The distinguishability of dimembers by adjacency"
  [family]

  (family-connectivity
   (set
    (filter
     (fn [coll]
       (apply = (map (partial adjacencies family) coll)))
     (multiselection (apply union family) #{1 2})))))

; Closure and interior
; Closure and interior are used on various set systems 
(defn ir
  [family subcoll]

  (if (set? family)
    (first (maximal-members (submembers family subcoll)))
    ((:interior family) subcoll)))

(defn missing-members
  [family subcoll]

  (difference (cl family subcoll) family))

(defn excess-members
  [family subcoll]

  (difference family (ir family subcoll)))

; Moore families
; After subclass closed families we introduce moore families
(defn singletonize
  [obj]

  #{obj})

; Rank complete families
(def rank-complete-family?
  (moore-family
   universal?
   (fn [family]
     (multiselection (apply union family) (set (map count family))))))

; Subnull and subsingleton closed
(def subnull-closed?
  (moore-family
   universal?
   (fn [coll]
     (if (empty? coll)
       coll
       (union #{#{}} coll)))))

(def subsingleton-closed?
  (moore-family
   universal?
   (fn [coll]
     (union
      coll
      (set
       (map
        (fn [i] #{i})
        (apply union coll)))))))

(def subunique-closed?
  (moore-family
   universal?
   (fn [coll]
     (union
      coll
      (if (empty? coll) #{} #{#{}})
      (set
       (map
        (fn [i] #{i})
        (apply union coll)))))))

(def null-family?
  (logical-interval
   #{#{}}
   universal?))

(def null-rank-one-family?
  (logical-interval
   (cardinality-classification #{0})
   (cardinality-classification #{0 1})))

(def null-singleton-free-rank-two-family?
  (logical-interval
   (cardinality-classification #{0})
   (cardinality-classification #{0 2})))

(def null-rank-two-family?
  (logical-interval
   (cardinality-classification #{0})
   (cardinality-classification #{0 1 2})))

; Unique families
(def rank-one-unique-family?
  (intersection
   rank-one-family?
   unique-family?))

(def rank-two-unique-family?
  (intersection
   rank-two-family?
   unique-family?))

(def nullfree-unique-family?
  (intersection
   nullfree-family?
   unique-family?))

(def unique-unary-family?
  (intersection
   unary-family?
   unique-family?))

(def nullfree-rank-two-unique-family?
  (intersection
   nullfree-rank-two-family?
   unique-family?))

(def unique-binary-family?
  (intersection
   binary-family?
   unique-family?))

(def nullfree-singular-family?
  (intersection
   nullfree-family?
   singular-universal?))

(def singular-binary-family?
  (intersection
   singular-family?
   binary-family?))

; Independency families
(defn unary-family
  "This is also equal to the trivial partition of the set."
  [coll]

  (selections coll 1))

(defn complement-independencies
  [family]

  (let [coll (apply union family)
        new-pairs(set
                  (filter
                   (fn [pair]
                     (not (contains? family pair)))
                   (selections coll 2)))]
    (union (unary-family (difference coll (apply union new-pairs)))
           new-pairs)))

(defn indeps
  [family]

  (let [appropriate-pairs (intersection
                           size-two-universal?
                           (apply union (map power-set (maximal-members family))))]
    (union appropriate-pairs
           (unary-family
            (difference
             (apply union family)
             (apply union appropriate-pairs))))))

(defn complete-independency-family
  [coll]

  (cond
    (empty? coll) #{}
    (= (count coll) 1) (unary-family coll)
    :else  (selections coll 2)))

(defn cluster-independency-family
  [coll]

  (apply
   union
   (map complete-independency-family coll)))

(def independency-family?
  (intersection
   sperner-family?
   nullfree-rank-two-family?))

(def uniquely-dependent-independency-family?
  (intersection
   uniquely-dependent-family?
   independency-family?))

(defn complete-independency-family?
  [family]

  (and
   (independency-family? family)
   (uniquely-dependent-family? family)
   (rank-complete-family? family)))

(defn cluster-independency-family?
  [family]

  (every?
   complete-independency-family?
   (adjacency-connected-components family)))

(defn cocluster-independency-family?
  [family]

  (cluster-independency-family? (complement-independencies family)))

(def regular-independency-family?
  (intersection
   regular-family?
   independency-family?))

(def regular-cocluster-independency-family?
  (intersection
   regular-independency-family?
   cocluster-independency-family?))

(def triangle-free-independency-family?
  (intersection
   triangle-free-family?
   independency-family?))

(defn rank-two-set-partition?
  [family]

  (and
   (independency-family? family)
   (every?
    (fn [i]
      (<= (count (apply union i)) 2))
    (adjacency-connected-components family))))

(def binary-set-division?
  (intersection
   binary-family?
   rank-two-set-partition?))

; Maximal cliques families
(defn blocker
  [family]

  (minimal-members
   (set
    (filter
     (fn [i]
       (every?
        (fn [j]
          (not (empty? (intersection i j))))
        family))
     (power-set (apply union family))))))

(defn maximal-cliques-family?
  [family]

  (= family (maximal-cliques family)))

(defn cocluster-maximal-cliques-family?
  [family]

  (let [coll (blocker family)]
    (and (independent-family? coll)
         (sperner-family? coll))))

(def regular-maximal-cliques-family?
  (intersection
   regular-family?
   maximal-cliques-family?))

(def regular-cocluster-maximal-cliques-family?
  (intersection
   regular-family?
   cocluster-maximal-cliques-family?))

; Sperner families
(def nullfree-sperner-family?
  (intersection
   nullfree-family?
   sperner-family?))

(def rank-one-sperner-family?
  (intersection
   sperner-family?
   rank-one-family?))

(def rank-two-sperner-family?
  (intersection
   sperner-family?
   rank-two-family?))

(defn independent-sperner-family?
  [family]

  (and
   (or
    (= (count family) 1)
    (not (contains? family #{})))
   (every?
    (fn [pair]
      (empty? (apply intersection pair)))
    (selections family 2))))

(defn set-partition?
  [family]

  (and
   (not (contains? family #{}))
   (every?
    (fn [pair]
      (empty? (apply intersection pair)))
    (selections family 2))))

(def rank-three-set-partition?
  (intersection
   rank-three-family?
   set-partition?))

(def rank-four-set-partition
  (intersection
   rank-four-family?
   set-partition?))

(defn linear-sperner-family?
  [family]

  (every?
   (fn [pair]
     (and
      (not (contains? pair (apply intersection pair)))
      (<= (count (apply intersection pair)) 1)))
   (selections family 2)))

(def nullfree-linear-sperner-family?
  (intersection
   linear-sperner-family?
   nullfree-family?))

(def triangle-free-sperner-family?
  (intersection
   triangle-free-family?
   sperner-family?))

(def bipartite-sperner-family?
  (intersection
   bipartite-family?
   sperner-family?))

(def regular-sperner-family?
  (intersection
   sperner-family?
   regular-family?))

(def uniquely-dependent-sperner-family?
  (intersection
   sperner-family?
   uniquely-dependent-family?))

(defn antidisjoint-sperner-family?
  [family]

  (every?
   (fn [pair]
     (and
      (not (empty? (apply intersection pair)))
      (not (contains? family (apply intersection pair)))))
   (selections family 2)))

(defn blocker-reducible-sperner-family?
  [family]

  (or
   (empty? family)
   (and
    (= (count family) 1)
    (<= (count (apply union family)) 1))
   (and
    (<= 2 (count (family-connectivity family)))
    (every? blocker-reducible-sperner-family? (adjacency-connected-components family)))
   (and
    (<= 2 (count (family-connectivity (blocker family))))
    (every? blocker-reducible-sperner-family? (adjacency-connected-components (blocker family))))))

(defn uniform-family?
  [family]

  (or
   (empty? family)
   (apply = (map count family))))

(def nullfree-uniform-family?
  (intersection
   nullfree-family?
   uniform-family?))

(def rank-two-uniform-family?
  (intersection
   uniform-family?
   rank-two-family?))

(defn independent-uniform-family?
  [family]

  (every?
   (fn [pair]
     (and
      (apply = (map count pair))
      (empty? (apply intersection pair))))
   (selections family 2)))

(defn set-division?
  [family]

  (and
   (nullfree-family? family)
   (every?
    (fn [pair]
      (and
       (apply = (map count pair))
       (empty? (apply intersection pair))))
    (selections family 2))))

(def ternary-set-division?
  (intersection
   ternary-family?
   set-division?))

(def quaternary-set-division?
  (intersection
   quaternary-family?
   set-division?))

(def linear-uniform-family?
  (intersection
   linear-sperner-family?
   uniform-family?))

(def nullfree-linear-uniform-family?
  (intersection
   linear-sperner-family?
   uniform-family?
   nullfree-family?))

(def antidisjoint-uniform-family?
  (intersection
   antidisjoint-sperner-family?
   uniform-family?))

(def regular-uniform-family?
  (intersection
   uniform-family?
   regular-family?))

(def uniquely-dependent-uniform-family?
  (intersection
   uniform-family?
   uniquely-dependent-family?))

(def matroid-bases-family?
  (intersection
   uniform-family?
   (fn [family]
     (every?
      (fn [pair]
        (let [[a b] (seq pair)]
          (every?
           (fn [i]
             (not
              (every?
               (complement
                (fn [j]
                  (contains? family (union (difference a #{i}) #{j}))))
               (difference b a))))
           (difference a b))))
      (selections family 2)))))

(defn complete-uniform-family?
  [coll]

  (or
   (empty? coll)
   (let [underlying-coll (apply union coll)
         size (apply min (map count coll))]
     (= coll (selections underlying-coll size)))))

(def complete-binary-family?
  (moore-family
   size-two-universal?
   (fn [family]
     (selections (apply union family) 2))))

(def complete-ternary-family?
  (moore-family
   size-three-universal?
   (fn [family]
     (selections (apply union family) 3))))

(def complete-quaternary-family?
  (moore-family
   size-four-universal?
   (fn [family]
     (selections (apply union family) 4))))

; Chain families
(defn kfirst
  [pair]

  (first (apply intersection pair)))

(defn ksecond
  [pair]

  (if (= (count pair) 1)
    (first (apply intersection pair))
    (first (difference (apply union pair) (apply intersection pair)))))

(defn kpair
  [pair]

  (if (= (first pair) (second pair))
    #{#{(first pair)}}
    #{#{(first pair)} #{(first pair) (second pair)}}))

(defn progression-family
  [& args]

  (set
   (map
    (fn [n]
      (set (take n args)))
    (range 1 (inc (count args))))))

(def nullfree-chain-family?
  (intersection
   nullfree-family?
   chain-family?))

(def rank-two-chain-family?
  (intersection
   rank-two-family?
   chain-family?))

(def nullfree-rank-two-chain-family?
  (intersection
   nullfree-rank-two-family?
   chain-family?))

(defn subnonnull-free-chain-family?
  [family]

  (or
   (<= (count family) 1)
   (and
    (contains? family #{})
    (= (count family) 2))))

(def subnull-free-chain-family?
  (intersection
   subnull-free?
   chain-family?))

(def subsingleton-free-chain-family?
  (intersection
   subsingleton-free?
   chain-family?))

(def subnonsingleton-free-chain-family?
  (intersection
   subnonsingleton-free?
   chain-family?))

(def subunique-free-chain-family?
  (intersection
   subunique-free?
   chain-family?))

(def subnonunique-free-chain-family?
  (intersection
   subnonunique-free?
   chain-family?))

(def singleton-isolated-chain-family?
  (intersection
   singleton-isolated-family?
   chain-family?))

(defn strongly-saturated-chain-family?
  [family]

  (or
   (<= (count family) 1)
   (and
    (= (count family) 2)
    (contains? family (apply intersection family))
    (= (count (difference (apply union family) (apply intersection family))) 1))))

(def strongly-antisaturated-chain-family?
  (intersection
   strongly-antisaturated-family?
   chain-family?))

(def nullfree-height-two-chain-family?
  (intersection
   nullfree-family?
   height-two-chain-family?))

(def trivial-alexandrov-family?
  (intersection
   null-family?
   subnonnull-free-chain-family?))

(defn kuratowski-pair?
  [family]

  (and
   (nullfree-height-two-chain-family? family)
   (<= 1 (count (apply union family)) 2)
   (unary-family? (distinguishability family))))

(def distinct-kuratowski-pair?
  (intersection
   size-two-universal?
   kuratowski-pair?))

(defn saturated-chain-family?
  [family]

  (let [coll (apply intersection family)]
    (and
     (chain-family? family)
     (unary-family?
      (distinguishability
       (set
        (map
         (fn [i]
           (difference i coll))
         family)))))))

(def nullfree-saturated-chain-family?
  (intersection
   saturated-chain-family?
   nullfree-family?))

(def kolmogorov-chain-family?
  (intersection
   chain-family?
   (comp unary-family? distinguishability)))

(def progression-family?
  (intersection
   chain-family?
   nullfree-family?
   (comp unary-family? distinguishability)))

(def subnull-closed-chain-family?
  (intersection
   chain-family?
   subnull-closed?))

(def chain-antimatroid?
  (intersection
   chain-family?
   subnull-closed?
   (comp unary-family? distinguishability)))

(def null-chain-family?
  (intersection
   null-family?
   chain-family?))

(def null-kolmogorov-chain-family?
  (intersection
   null-family?
   chain-antimatroid?))

; Weak height two multichain
(defn independent-multichain-family?
  [family]

  (or
   (independent-sperner-family? family)
   (and
    (contains? family #{})
    (= (count family) 2))))

; Height two multichains
(def nullfree-height-two-multichain-family?
  (intersection
   nullfree-family?
   height-two-multichain-family?))

(defn laminar-height-two-multichain-family?
  [family]

  (let [components (order-connected-components family)]
    (and
     (every? (fn [i] (<= (count i) 2)) components)
     (independent-sperner-family? (set (map (partial apply union) components))))))

(def nullfree-laminar-height-two-multichain-family?
  (intersection
   nullfree-family?
   laminar-height-two-multichain-family?))

(def height-two-multiprogression-family?
  (intersection
   nullfree-family?
   (comp unary-family? distinguishability)
   laminar-height-two-multichain-family?))

; Multichains
(def nullfree-multichain-family?
  (intersection
   nullfree-family?
   multichain-family?))

(defn laminar-multichain-family?
  [family]

  (let [components (order-connected-components family)]
    (and
     (every? chain-family? components)
     (independent-sperner-family? (set (map (partial apply union) components))))))

(def nullfree-laminar-multichain-family?
  (intersection
   nullfree-family?
   laminar-multichain-family?))

(def multiprogression-family?
  (intersection
   nullfree-family?
   (comp unary-family? distinguishability)
   laminar-multichain-family?))

; Dependency families
; This is an entire section dedicated to dealing with dependency families
; based upon the principles of graph theory
(defn all-paths
  ([family start-node end-node]
   (set (all-paths family start-node end-node #{start-node})))
  ([family start-node end-node visited-nodes]

   (let [coll (difference
               (adjacencies family start-node)
               visited-nodes)]
     (mapcat
      (fn [i]
        (if (= i end-node)
          (list (list start-node end-node))
          (map
           (partial cons start-node)
           (all-paths family i end-node (conj visited-nodes i)))))
      coll))))

(defn shortest-paths
  [family a b]

  (let [paths (all-paths family a b)]
    (set
     (if (empty? paths)
       '()
       (let [shortest-path-length (apply min (map count paths))]
         (filter
          (comp (partial = shortest-path-length) count)
          paths))))))

(defn maximal-paths
  ([family start-node]
   (maximal-paths family start-node #{start-node}))
  ([family start-node visited-nodes]

   (let [coll (difference (adjacencies family start-node) visited-nodes)]
     (if (empty? coll)
       (list (list start-node))
       (mapcat
        (fn [i]
          (map (partial cons start-node) (maximal-paths family i (conj visited-nodes i))))
        coll)))))

(defn longest-path-length
  [family]

  (let [coll (mapcat (partial maximal-paths family) (apply union family))]
    (if (empty? coll)
      0
      (apply max (map count coll)))))

; Distance and shortest paths
(defn dijkstra
  [family current-node target-node tentative-distances unvisited-nodes]

  (let [unvisited-neighbours (intersection
                              unvisited-nodes
                              (adjacencies family current-node))
        new-distances (merge
                       tentative-distances
                       (into
                        {}
                        (map
                         (fn [i]
                           (let [new-distance
                                 (min
                                  (get tentative-distances i)
                                  (inc (get tentative-distances current-node)))]
                             [i new-distance]))
                         unvisited-neighbours)))
        new-unvisited-nodes (disj unvisited-nodes current-node)]
    (if (not (contains? new-unvisited-nodes target-node))
      (get tentative-distances target-node)
      (let [remaining-distances (map new-distances new-unvisited-nodes)
            new-smallest-distance (if (empty? remaining-distances)
                                    Double/POSITIVE_INFINITY
                                    (apply min remaining-distances))]
        (if (= Double/POSITIVE_INFINITY new-smallest-distance)
          Double/POSITIVE_INFINITY
          (let [new-current-node (first
                                  (filter
                                   (fn [i]
                                     (= (get new-distances i)
                                        new-smallest-distance))
                                   new-unvisited-nodes))]
            (dijkstra
             family
             new-current-node
             target-node
             new-distances
             new-unvisited-nodes)))))))

(defn path-distance
  [family a b]

  (let [dimembers (apply union family)
        start-distances (into
                         {}
                         (map
                          (fn [i]
                            [i (if (= i a)
                                 0
                                 Double/POSITIVE_INFINITY)])
                          dimembers))]
    (dijkstra family a b start-distances dimembers)))

(defn eccentricity
  [family a]

  (let [distances (map
                   (fn [i]
                     (path-distance family a i))
                   (apply union family))]
    (apply max distances)))

(defn diameter
  [family]

  (let [coll (apply union family)]
    (if (empty? coll)
      0
      (apply max (map (partial eccentricity family) coll)))))

(defn radius
  [family]

  (let [coll (apply union family)]
    (if (empty? coll)
      0
      (apply min (map (partial eccentricity family) coll)))))

(defn central-vertices
  [family]

  (set
   (let [current-radius (radius family)]
     (filter
      (fn [i]
        (= (eccentricity family i) current-radius))
      (apply union family)))))

(defn peripheral-vertices
  [family]

  (set
   (let [current-diameter (diameter family)]
     (filter
      (fn [i]
        (= (eccentricity family i) current-diameter))
      (apply union family)))))

(defn metric-ball
  [family a radius]

  (set
   (filter
    (fn [i]
      (<= (path-distance family i a) radius))
    (apply union family))))

(defn metric-interval
  [family a b]

  (if (= a b)
    #{a}
    (apply union (map set (shortest-paths family a b)))))

(defn metric-intervals
  [family]

  (union
   (multiselection (apply union family) #{0 1})
   (set
    (for [pair (selections (apply union family) 2)
          :let [[a b] (seq pair)]]
      (metric-interval family a b)))))

(defn rooted-intervals
  [family a]

  (set
   (map
    (fn [i]
      (metric-interval family a i))
    (apply union family))))

; Dependency family utilities
(defn complement-dependencies
  [family]

  (let [coll (apply union family)]
    (union
     (unary-family (apply union family))
     (set
      (filter
       (fn [pair]
         (not (contains? family pair)))
       (selections coll 2))))))

(defn family-coconnectivity
  [family]

  (family-connectivity (complement-dependencies family)))

(defn deps
  [family]

  (intersection
   (multiselection entity? #{1 2})
   (apply union (map power-set (maximal-members family)))))

(defn subdeps
  [family coll]

  (deps (subfamily family coll)))

(defn neighbourhood-dependencies
  [family i]

  (subfamily family (disj (adjacencies family i) i)))

(defn dependency-component
  [family]

  (if (set? family)
    (set
     (filter
      (fn [i]
        (or
         (singular-universal? i)
         (and
          (size-two-universal? i)
          (every? (fn [elem] (contains? family #{elem})) i))))
      family))
    (Universal.
     (fn [i]
       (or
        (and
         (singular-universal? i)
         (family i))
        (and
         (size-two-universal? i)
         (family i)
         (every? (fn [elem] (family #{elem})) i)))))))

; Special classes of vertices
(defn leaf-vertices
  [family]

  (set
   (filter
    (fn [i]
      (= (adjacency-degree family i) 2))
    (apply union family))))

(defn dominating-vertices
  [family]

  (set
   (filter
    (fn [i]
      (= (adjacency-degree family i) (count (apply union family))))
    (apply union family))))

; We need to be able to deal with centralizers of dependency families
; and from these it would be nice if we could form associated
; intersection closed families
(defn dependency-centralizer
  [family coll]

  (let [dimembers (apply union family)]
    (set
     (filter
      (fn [i]
        (every?
         (fn [j]
           (contains? family (set (list i j))))
         coll))
      dimembers))))

(defn dependency-centralizers
  [family]

  (set
   (map
    (fn [coll]
      (dependency-centralizer family coll))
    (power-set (apply union family)))))

; Generate specific types of dependency families
(defn cluster-dependency-family
  [coll]

  (apply union (map (fn [i] (multiselection i #{1 2})) coll)))

(defn cocluster-dependency-family
  [coll]

  (complement-dependencies (cluster-dependency-family coll)))

(defn complete-dependency-family
  [coll]

  (multiselection coll #{1 2}))

; Basic classes of dependency families
(def dependency-family?
  (moore-family
   (cardinality-classification #{1 2})
   (fn [coll]
     (union coll (set (map (fn [i] #{i}) (apply union coll)))))))

(def complete-dependency-family?
  (moore-family
   (multiselection entity? #{1 2})
   (fn [family]
     (multiselection (apply union family) #{1 2}))))

; Forbidden dependency families of size three
(def triangle-free-dependency-family?
  (intersection
   triangle-free-family?
   dependency-family?))

(def cotriangle-free-dependency-family?
  (intersection
   dependency-family?
   (comp triangle-free-family? complement-dependencies)))

(def cluster-dependency-family?
  (moore-family
   (multiselection entity? #{1 2})
   (comp cluster-dependency-family family-connectivity)))

(def cocluster-dependency-family?
  (intersection
   dependency-family?
   (comp cluster-dependency-family? complement-dependencies)))

(def bicluster-dependency-family?
  (union
   unary-family?
   complete-dependency-family?))

(def triangle-free-cluster-dependency-family?
  (intersection
   triangle-free-dependency-family?
   cluster-dependency-family?))

(def triangle-free-cocluster-dependency-family?
  (intersection
   triangle-free-dependency-family?
   cocluster-dependency-family?))

(def triangle-free-bicluster-dependency-family?
  (intersection
   triangle-free-dependency-family?
   bicluster-dependency-family?))

(def cotriangle-free-cluster-dependency-family?
  (intersection
   cotriangle-free-dependency-family?
   cluster-dependency-family?))

(def cotriangle-free-cocluster-dependency-family?
  (intersection
   cotriangle-free-dependency-family?
   cocluster-dependency-family?))

(def cotriangle-free-bicluster-dependency-family?
  (intersection
   cotriangle-free-dependency-family?
   bicluster-dependency-family?))

(def max-order-two-dependency-family?
  (intersection
   max-order-two-family?
   dependency-family?))

; Forbbiden dependency families of size four
(defn four-clique-free-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (<= (clique-number family) 3)))

(defn locally-cluster-dependency-family?
  [family]

  (every?
   (fn [i]
     (cluster-dependency-family? (neighbourhood-dependencies family i)))
   (apply union family)))

(defn locally-cocluster-dependency-family?
  [family]

  (every?
   (fn [i]
     (cocluster-dependency-family? (neighbourhood-dependencies family i)))
   (apply union family)))

(defn locally-cotriangle-free-dependency-family?
  [family]

  (every?
   (fn [i]
     (cotriangle-free-dependency-family? (neighbourhood-dependencies family i)))
   (apply union family)))

(defn colocally-triangle-free-dependency-family?
  [family]

  (locally-cotriangle-free-dependency-family? (complement-dependencies family)))

(defn colocally-cluster-dependency-family?
  [family]

  (locally-cocluster-dependency-family? (complement-dependencies family)))

(defn colocally-cocluster-dependency-family?
  [family]

  (locally-cluster-dependency-family? (complement-dependencies family)))

(defn four-coclique-free-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (<= (independence-number family) 3)))

(defn square-free-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (every?
    (complement
     (fn [subfamily]
       (every?
        (fn [i]
          (= 3 (count (adjacencies subfamily i))))
        (apply union family))))
    (selections family 4))))

(def cosquare-free-dependency-family?
  (intersection
   dependency-family?
   (comp square-free-dependency-family? complement-dependencies)))

(defn complement-reducible-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (or
    (<= (count family) 1)
    (and
     (<= 2 (count (adjacency-connected-components family)))
     (every? complement-reducible-dependency-family? (adjacency-connected-components family)))
    (and
     (<= 2 (count (adjacency-connected-components (complement-dependencies family))))
     (every? complement-reducible-dependency-family? (adjacency-connected-components (complement-dependencies family)))))))

; Locality conditions
(def locally-bicluster-dependency-family?
  (intersection
   locally-cluster-dependency-family?
   locally-cocluster-dependency-family?))

(def locally-cotriangle-free-cluster-dependency-family?
  (intersection
   locally-cotriangle-free-dependency-family?
   locally-cluster-dependency-family?))

(def locally-cotriangle-free-cocluster-dependency-family?
  (intersection
   locally-cotriangle-free-dependency-family?
   locally-cocluster-dependency-family?))

(def locally-cotriangle-free-bicluster-dependency-family?
  (intersection
   locally-cluster-dependency-family?
   locally-cocluster-dependency-family?
   locally-cotriangle-free-bicluster-dependency-family?))

(defn bilocal-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (every?
    (fn [i]
      (<= (count (adjacencies family i)) 3))
    (apply union family))))

; Threshold type dependency families
(defn trivially-perfect-dependency-family?
  [family]

  (letfn [(trivially-perfect-family? [family]
            (every?
             (fn [component]
               (let [coll (apply union component)
                     total-elements (set
                                     (filter
                                      (fn [i]
                                        (= (adjacencies component i) coll))
                                      coll))]
                 (and
                  (not (empty? total-elements))
                  (trivially-perfect-family?
                   (subfamily component (difference coll total-elements))))))
             (adjacency-connected-components family)))]
    (and
     (dependency-family? family)
     (trivially-perfect-family? family))))

(def cotrivially-perfect-dependency-family?
  (intersection
   dependency-family?
   (comp trivially-perfect-dependency-family? complement-dependencies)))

(def pseudo-split-dependency-family?
  (intersection
   square-free-dependency-family?
   cosquare-free-dependency-family?))

(def threshold-dependency-family?
  (intersection
   trivially-perfect-dependency-family?
   cotrivially-perfect-dependency-family?))

; Combined conditions locality and otherwise
(def weakly-geodetic-dependency-family?
  (intersection
   square-free-dependency-family?
   locally-cluster-dependency-family?))

(def bilocal-trivially-perfect-dependency-family?
  (intersection
   bilocal-family?
   trivially-perfect-dependency-family?))

; Additional classes of dependency families
(def max-order-three-dependency-family?
  (intersection
   max-order-three-family?
   dependency-family?))

(defn threshold-cluster-dependency-family?
  [family]

  (let [connectivity (family-connectivity family)]
    (and
     (<= (count (set (filter (complement singular-universal?) connectivity))) 1)
     (= family (cluster-dependency-family connectivity)))))

(def threshold-cocluster-dependency-family?
  (intersection
   cocluster-dependency-family?
   threshold-dependency-family?))

; Forbid classes of size five
(def max-order-four-dependency-family?
  (intersection
   max-order-four-family?
   dependency-family?))

; Perfect dependency families
(defn perfect-dependency-family?
  [family]

  (letfn [(forbidden-component? [current-family]
            (and
             (uniquely-dependent-family? current-family)
             (let [coll (apply union current-family)
                   degrees (map (comp count (partial adjacencies current-family)) coll)]
               (or
                (every? (partial = 3) degrees)
                (every? (partial = (- (count coll) 2)) degrees)))))]
    (and
     (dependency-family? family)
     (every?
      (fn [component]
        (let [component-coll (apply union component)]
          (or
           (<= (count (apply union component-coll)) 4)
           (every?
            (fn [n]
              (every?
               (fn [current-coll]
                 (not (forbidden-component? (subfamily component current-coll))))
               (selections component-coll n)))
            (range 5 (inc (count component-coll)) 2)))))
      (adjacency-connected-components family)))))

(defn comparability-dependency-family?
  [family]

  (letfn [(orientations [coll]
            (let [pairs (map
                         (fn [i]
                           (let [[a b] (seq i)]
                             (list (list a b) (list b a))))
                         coll)]
              (set
               (map
                (fn [nums]
                  (set
                   (map
                    (fn [i]
                      (if (contains? nums i)
                        (first (nth pairs i))
                        (second (nth pairs i))))
                    (range (count coll)))))
                (power-set (set (range (count coll))))))))
          (transitive-orientation? [coll]
            (every?
             (fn [current-coll]
               (let [[[a b] [c d]] (seq current-coll)]
                 (cond
                  (and
                   (not= a b)
                   (not= a d)
                   (not=  b d)
                   (= b c))
                  (contains? coll (list a d))
                  (and
                   (not= a b)
                   (not= a c)
                   (not= b c)
                   (= d a))
                  (contains? coll (list c b))
                  :else
                  true)))
             (selections coll 2)))]
    (and
     (dependency-family? family)
     (every?
      (fn [current-family]
        (or
         (<= (count (apply union current-family)) 4)
         (let [pairs (intersection size-two-universal? current-family)]
           (not
            (every?
             (complement
              transitive-orientation?)
             (orientations pairs))))))
      (adjacency-connected-components family)))))

(def cocomparability-dependency-family?
  (intersection
   dependency-family?
   (comp comparability-dependency-family? complement-dependencies)))

(def permutation-dependency-family?
  (intersection
   comparability-dependency-family?
   cocomparability-dependency-family?))

(defn weakly-chordal-dependency-family?
  [family]

  (letfn [(forbidden-component? [current-family]
            (and
             (uniquely-dependent-family? current-family)
             (let [coll (apply union current-family)
                   degrees (map (comp count (partial adjacencies current-family)) coll)]
               (or
                (every? (partial = 3) degrees)
                (every? (partial = (- (count coll) 2)) degrees)))))]
    (and
     (dependency-family? family)
     (every?
      (fn [component]
        (let [component-coll (apply union component)]
          (or
           (<= (count (apply union component-coll)) 4)
           (every?
            (fn [n]
              (every?
               (fn [current-coll]
                 (not (forbidden-component? (subfamily component current-coll))))
               (selections component-coll n)))
            (range 5 (inc (count component-coll)))))))
      (adjacency-connected-components family)))))

(defn chordal-dependency-family?
  [family]

  (letfn [(hole? [current-family]
            (and
             (uniquely-dependent-family? current-family)
             (every?
              (fn [i]
                (= 3 (count (adjacencies current-family i))))
              (apply union current-family))))]
    (and
     (dependency-family? family)
     (every?
      (fn [coll]
        (or
         (<= (count (apply union coll)) 3)
         (not (hole? (subfamily family coll)))))
      (power-set (apply union family))))))

(def cochordal-dependency-family?
  (intersection
   dependency-family?
   (comp chordal-dependency-family? complement-dependencies)))

(def split-dependency-family?
  (intersection
   chordal-dependency-family?
   cochordal-dependency-family?))

(def bipartite-dependency-family?
  (intersection
   bipartite-family?
   dependency-family?))

(def bipartite-permutation-dependency-family?
  (intersection
   bipartite-dependency-family?
   (comp comparability-dependency-family? complement-dependencies)))

(defn undirected-forest?
  [family]

  (letfn [(cycle-free? [component past-elements previous-elements current-node]
            (let [next-elements (clojure.set/difference
                                 (adjacencies component current-node)
                                 (union previous-elements #{current-node}))]
              (cond
               (empty? next-elements) true
               (not (empty? (intersection past-elements next-elements))) false
               :else (every?
                      (fn [next-element]
                        (cycle-free?
                         component
                         (union past-elements previous-elements)
                         #{current-node}
                         next-element))
                      next-elements))))]
    (and
     (dependency-family? family)
     (every?
      (fn [coll]
        (cycle-free? coll #{} #{} (first (apply union coll))))
      (adjacency-connected-components family)))))

(defn multipath-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (every?
    (fn [component]
      (let [coll (apply union component)
            degrees (map (comp count (partial adjacencies family)) coll)]
        (or
         (<= (count coll) 2)
         (and
          (not (apply = degrees))
          (every? (fn [degree] (<= degree 3)) degrees)))))
    (adjacency-connected-components family))))

(def cobipartite-dependency-family?
  (intersection
   dependency-family?
   (comp bipartite-family? complement-dependencies)))

(def cobipartite-permutation-dependency-family?
  (intersection
   cobipartite-dependency-family?
   comparability-dependency-family?))

; Uniquely connected dependency families
(def uniquely-connected-dependency-family?
  (intersection
   uniquely-connected-family?
   dependency-family?))

(def connected-dependency-family?
  (intersection
   uniquely-connected-family?
   dependency-family?
   (fn [family]
     (not (empty? family)))))

; Cactus trees containing cycles and paths
(def undirected-tree?
  (intersection
   undirected-forest?
   uniquely-connected-family?))

(defn path-dependency-family?
  [family]

  (let [coll (apply union family)
        degrees (map (comp count (partial adjacencies family)) coll)]
    (and
     (uniquely-connected-family? family)
     (dependency-family? family)
     (every?
      (fn [degree]
        (<= degree 3))
      degrees)
     (or
      (<= (count degrees) 2)
      (not (apply = degrees))))))

(defn caterpillar-tree?
  [family]

  (and
   (undirected-tree? family)
   (path-dependency-family?
    (subfamily
     family
     (difference (apply union family) (leaf-vertices family))))))

(defn star-dependency-family?
  [family]

  (let [coll (dominating-vertices family)]
    (and (<= (count coll) 1)
         (unary-family? (subfamily family (difference (apply union family) coll))))))

(defn cycle-dependency-family?
  [family]

  (and
   (uniquely-connected-family? family)
   (dependency-family? family)
   (or
    (<= (count (apply union family)) 2)
    (every?
     (fn [i]
       (= 3 (count (adjacencies family i))))
     (apply union family)))))

(defn multicycle-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (every?
    (fn [component]
      (or
       (<= (count (apply union component)) 2)
       (every?
        (fn [i]
          (= 3 (count (adjacencies component i))))
        (apply union component))))
    (adjacency-connected-components family))))

; Specific dependency families
(def order-two-dependency-family?
  (intersection
   order-two-family?
   dependency-family?))

(def order-three-dependency-family?
  (intersection
   order-three-family?
   dependency-family?))

(def order-four-dependency-family?
  (intersection
   order-four-family?
   dependency-family?))

(def regular-dependency-family?
  (intersection
   dependency-family?
   regular-family?))

(def regular-cluster-dependency-family?
  (intersection
   regular-family?
   cluster-dependency-family?))

(def regular-cocluster-dependency-family?
  (intersection
   regular-family?
   cocluster-dependency-family?))

; Wheel graphs
(defn wheel-dependency-family?
  [family]

  (or
   (empty? family)
   (let [coll (dominating-vertices family)]
     (and
      (not (empty? coll))
      (cycle-dependency-family?
       (subfamily
        family
        (disj (apply union family) (first coll))))))))

; Path related dependency families
(defn traceable-dependency-family?
  [family]

  (= (longest-path-length family) (count (apply union family))))

; Metric related classes of families
(defn self-centered-dependency-family?
  [family]

  (= (diameter family)
     (radius family)))

; Additional connectivity
(defn cut-vertices
  [family]

  (set
   (filter
    (fn [i]
      (not
       (connected-dependency-family?
        (subfamily family (disj (apply union family) i)))))
    (apply union family))))

(defn cut-sets
  [family]

  (if (connected-dependency-family? family)
    (set
     (filter
      (fn [coll]
        (not
         (connected-dependency-family?
          (subfamily family (difference (apply union family) coll)))))
      (power-set (apply union family))))
    #{#{}}))

(defn cut-edges
  [family]

  (set
   (filter
    (fn [i]
      (not
       (connected-dependency-family?
        (disj family i))))
    (intersection size-two-universal? family))))

(defn cut-edge-sets
  [family]

  (if (connected-dependency-family? family)
    (set
     (filter
      (fn [coll]
        (not
         (connected-dependency-family?
          (difference family coll))))
      (power-set (intersection size-two-universal? family))))
    #{#{}}))

(defn vertex-connectivity
  [family]

  (apply min (map count (cut-sets family))))

(defn edge-connectivity
  [family]

  (apply min (map count (cut-edge-sets family))))

(defn biconnected-dependency-family?
  [family]

  (and
   (<= 2 (count (apply union family)))
   (uniquely-connected-dependency-family? family)
   (empty? (cut-vertices family))))

(defn block-dependency-family?
  [family]

  (every?
   (fn [coll]
     (complete-dependency-family? (subfamily family coll)))
   (subfamilies biconnected-dependency-family? family)))

(defn cactus-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (every?
    (fn [coll]
      (cycle-dependency-family? (subfamily family coll)))
    (subfamilies biconnected-dependency-family? family))))

(defn bridgeless-dependency-family?
  [family]

  (and
   (dependency-family? family)
   (empty? (cut-edges family))))

; Block sets
(defn block-sets
  [family]

  (maximal-members (subfamilies biconnected-dependency-family? family)))

(defn nontrivial-block-sets
  [family]

  (set (filter (fn [i] (<= 3 (count i))) (block-sets family))))

(defn unblocked-vertices
  [family]

  (union
   (cut-vertices family)
   (difference (apply union family)
               (apply union (nontrivial-block-sets family)))))

(defn maximum-block-size
  [family]

  (rank (subfamilies biconnected-dependency-family? family)))

; Clique seperators used with chordal graphs
(defn clique-seperators
  [family]

  (set
   (intersection
    (subfamilies complete-dependency-family? family)
    (cut-sets family))))

; Cactus dependency families
(defn pseudoforest-dependency-family?
  [family]

  (and
   (cactus-dependency-family? family)
   (<= (count (nontrivial-block-sets family)) 1)))

(defn tadpole-dependency-family?
  [family]

  (and
   (cactus-dependency-family? family)
   (let [blocks (nontrivial-block-sets family)
         cuts (cut-vertices family)]
     (and
      (<= (count blocks) 1)
      (path-dependency-family?
       (subfamily family (difference
                          (apply union family)
                          (difference
                           (apply union blocks)
                           cuts))))))))

(defn triangular-cactus-dependency-family?
  [family]

  (and (dependency-family? family)
       (<= (maximum-block-size family) 3)))

; Block dependency families
(defn single-clique-block-dependency-family?
  [family]

  (and
   (block-dependency-family? family)
   (<= (count (nontrivial-block-sets family)))))

(defn lollipop-dependency-family?
  [family]

  (and
   (single-clique-block-dependency-family? family)
   (path-dependency-family? (subfamily family (unblocked-vertices family)))))

(defn windmill-dependency-family?
  [family]

  (let [coll (dominating-vertices family)]
    (and (<= (count coll) 1)
         (cluster-dependency-family? (subfamily family (difference (apply union family) coll))))))

(defn friendship-dependency-family?
  [family]

  (let [coll (dominating-vertices family)]
    (and (<= (count coll) 1)
         (let [remaining-family (subfamily family (difference (apply union family) coll))]
           (and
            (cluster-dependency-family? remaining-family)
            (every? size-two-universal? (family-connectivity remaining-family)))))))

; Block cut tree
(defn bcset
  [family]

  (union (unary-family (cut-vertices family))
         (block-sets family)))

(defn bctree
  [family]

  (let [coll (bcset family)]
    (set
     (filter
      (fn [pair]
        (or
          (singular-universal? pair)
          (let [[a b] (seq pair)]
            (or
              (superset? (list a b))
              (superset? (list b a))))))
      (multiselection coll #{1 2})))))

(defn bcpath
  [family a b]

  (letfn [(total-betweenness [family a b]
            (if (= a b)
              #{a}
              (apply union (map set (all-paths family a b)))))]
    (let [tree (bctree family)
          coll (bcset family)]
      (total-betweenness tree (subdimembers coll a) (subdimembers coll b)))))

(defn bcinterval
  [family a b]

  (if (= a b)
    #{a}
    (apply union (bcpath family a b))))

(defn bcintervals
  [family]

  (let [coll (apply union family)]
    (union
     (multiselection coll #{0 1})
     (let [pairs (apply union (map #(selections % 2) (family-connectivity family)))]
       (set
        (map
         (fn [pair]
           (let [[a b] (seq pair)]
             (bcinterval family a b)))
         pairs))))))

; Vertex betweenness
(defn remove-vertex
  [family i]

  (subfamily family (disj (apply union family) i)))

(defn vertex-betweenness
  [family a b]

  (let [a-component (adjacencies (family-connectivity (remove-vertex family b)) a)
        b-component (adjacencies (family-connectivity (remove-vertex family a)) b)]
    (intersection a-component b-component)))

; Modular decomposition
(defn modular-subset?
  [family coll]

  (let [all-elements (apply union family)
        remaining-elements (difference all-elements coll)]
    (every?
     (fn [i]
       (or
        (every?
         (fn [v]
           (contains? family #{i v}))
         coll)
        (every?
         (fn [v]
           (not (contains? family #{i v})))
         coll)))
     remaining-elements)))

(defn modular-subsets
  [family]

  (set
   (filter
    (fn [coll]
      (modular-subset? family coll))
    (disj (power-set (apply union family)) #{}))))

(defn maximal-proper-modules
  [family]

  (maximal-members (disj (modular-subsets family) (apply union family))))

(defn complementary-decomposition
  [family]

  (let [coll (apply union family)
        components (family-connectivity family)]
    (if (= (count components) 1)
      (if (<= (count coll) 1)
        (unary-family coll)
        (let [cocomponents (family-connectivity (complement-dependencies family))]
          (if (= (count cocomponents) 1)
            #{coll}
            (complementary-decomposition (complement-dependencies family)))))
      (conj (apply union (map (comp complementary-decomposition (partial subfamily family)) components)) coll))))

(defn modular-decomposition
  [family]

  (let [coll (apply union family)
        components (family-connectivity family)]
    (if (= (count components) 1)
      (if (<= (count coll) 1)
        (unary-family coll)
        (let [cocomponents (family-connectivity (complement-dependencies family))]
          (if (= (count cocomponents) 1)
            (let [modules (maximal-proper-modules family)]
              (if (empty? modules)
                #{coll}
                (conj
                 (apply
                  union
                  (map
                   (comp modular-decomposition (partial subfamily family))
                   (maximal-proper-modules family)))
                 coll)))
            (modular-decomposition (complement-dependencies family)))))
      (conj (apply union (map (comp modular-decomposition (partial subfamily family)) components)) coll))))

; Height two strongly unique extrema
(def linear-height-two-family?
  (intersection
   linear-family?
   (union
    subnull-free?
    subsingleton-free?)))

(def nullfree-linear-family?
  (intersection
   nullfree-family?
   linear-family?))

(def rank-complete-convex-height-two-family?
  (intersection
   rank-complete-family?
   strongly-saturated-family?))

(def uniquely-connected-convex-height-two-family?
  (intersection
   uniquely-connected-family?
   strongly-saturated-family?))

; Height two families
(def subnonunique-free-height-two-family?
  (union
   subnonnull-free?
   subnonsingleton-free?))

(def regular-height-two-family?
  (intersection
   regular-family?
   height-two-family?))

(def rank-complete-height-two-family?
  (intersection
   rank-complete-family?
   height-two-family?))

; Inclusion unrestricted families
(defn complementary-family
  [family]

  (let [minima (apply intersection family)
        maxima (apply union family)]
    (set
     (map
      (fn [i]
        (union
         minima
         (difference maxima i)))
      family))))

; Common extrema free families
(defn common-extrema-irreducible-members
  [family]

  (set
   (filter
    (fn [i]
      (or
       (every?
        (complement
         (fn [coll]
           (and
            (<= 2 (count coll))
            (= i (apply intersection coll)))))
        (power-set family))
       (every?
        (complement
         (fn [coll]
           (and
            (<= 2 (count coll))
            (= i (apply union coll)))))
        (power-set family))))
    family)))

(defn intersection-irreducible-members
  [family]

  (set
   (filter
    (fn [i]
      (not
       (= i
          (apply
           intersection
           (set
            (filter
             (fn [coll]
               (and
                 (not= coll i)
                 (superset? (list i coll))))
             family))))))
    family)))

(defn union-irreducible-members
  [family]

  (set
   (filter
    (fn [i]
      (or
       (empty? i)
       (not
        (= i
           (apply
            union
            (difference (subfamily family i) #{i}))))))
    family)))

(defn extrema-irreducible-members
  [family]

  (intersection (intersection-irreducible-members family) (union-irreducible-members family)))

(defn common-extrema-free?
  [family]

  (every?
   (fn [coll]
     (not
      (let [maxima (maximal-members coll)
            minima (minimal-members coll)]
        (and
         (= (count maxima) 2)
         (= (count minima) 2)
         (= (apply union minima) (apply intersection maxima))
         (contains? family (apply union minima))))))
   (selections family 4)))
                                       
(defn intersection-free?
  [family]

  (= family (intersection-irreducible-members family)))

(defn union-free?
  [family]

  (= family (union-irreducible-members family)))

(def extrema-free?
  (intersection
   union-free?
   intersection-free?))

; Minimal and maximal union members
(defn minimal-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (every?
       (fn [j]
         (or
          (= i j)
          (not (contains? (subdimembers family i) j))))
       (apply union family)))
    (apply union family))))

(defn maximal-dimembers
  [family]

  (set
   (filter
    (fn [i]
      (every?
       (fn [j]
         (or
          (= i j)
          (not (contains? (superdimembers family i) j))))
       (apply union family)))
    (apply union family))))

(defn isolated-dimembers
  [family]

  (intersection (minimal-dimembers family) (maximal-dimembers family)))

(defn extremal-dimembers
  [family]

  (union (minimal-dimembers family) (maximal-dimembers family)))

; Suprema and infima
(defn upper-bound-dimembers
  [family coll]

  (set
   (filter
    (fn [i]
      (every?
       (fn [j]
         (contains? (superdimembers family j) i))
       coll))
    (apply union family))))

(defn lower-bound-dimembers
  [family coll]

  (set
   (filter
    (fn [i]
      (every?
       (fn [j]
         (contains? (superdimembers family i) j))
       coll))
    (apply union family))))

(defn suprema-dimembers
  [family coll]

  (let [elems (upper-bound-dimembers family coll)]
    (set
     (filter
      (fn [i]
        (every?
         (fn [j]
           (or
            (= i j)
            (not (contains? (subdimembers family i) j))))
         elems))
      elems))))

(defn infima-dimembers
  [family coll]

  (let [elems (lower-bound-dimembers family coll)]
    (set
     (filter
      (fn [i]
        (every?
         (fn [j]
           (or
            (= i j)
            (not (contains? (subdimembers family j) i))))
         elems))
      elems))))

(defn join-dimembers
  [family coll]

  (first (suprema-dimembers family coll)))

(defn meet-dimembers
  [family coll]

  (first (infima-dimembers family coll)))

; Join irreducibles
(defn join-irreducible-dimembers
  [family]

  (difference
   (apply union family)
   (apply
    union
    (map
     (fn [partition]
       (if (<= (count partition) 1)
         #{}
         (let [coll (apply union partition)
               suprema (suprema-dimembers family coll)]
           (if (and
                 (singular-universal? suprema)
                 (not (superset? (list suprema coll))))
             suprema
             #{}))))
     (power-set (distinguishability family))))))

(defn strongly-join-irreducible-dimembers
  [family]

  (difference
   (join-irreducible-dimembers family)
   (if (unique-minima-family? family)
     (minimal-dimembers family)
     #{})))

; Suprema irreducible dimembers
(defn suprema-irreducible-dimembers
  [family]

  (difference
   (set
    (filter
     (fn [i]
       (not (<= 2 (count (direct-subdimembers family i)))))
     (apply union family)))
   (let [minima (minimal-dimembers family)]
     (if (= (count minima) 1)
       #{(first minima)}
       #{}))))

; Related dependency families
(defn order-comparability
  [family]

  (let [coll (apply union family)]
    (union
     (unary-family coll)
     (set
      (filter
       (fn [pair]
         (let [[a b] (seq pair)]
           (or
            (contains? (subdimembers family a) b)
            (contains? (subdimembers family b) a))))
       (selections coll 2))))))

(defn covering-pairs
  [family]

  (let [coll (apply union family)]
    (union
     (unary-family coll)
     (set
      (filter
       (fn [pair]    
         (let [set-pair (set (map (fn [i] (cl family #{i})) pair))
               minima (apply intersection set-pair)
               maxima (apply union set-pair)
               remaining-elements (difference coll pair)]
           (and
            (contains? set-pair minima)
            (every?
             (fn [current-elem]
               (let [current-set (cl family #{current-elem})]
                 (not
                   (and
                     (superset? (list minima current-set))
                     (superset? (list current-set maxima))))))
             remaining-elements))))
       (selections coll 2))))))

; Order intervals
(defn order-interval
  [family a b]

  (intersection (superdimembers family a)
                (subdimembers family b)))

(defn order-intervals
  [family]

  (let [coll (apply union family)]
    (union
     (multiselection coll #{0 1})
     (set
      (for [pair (selections coll 2)
            :let [[a b] (seq pair)]
            :let [suborder (cond
                             (contains? (subdimembers family a) b)
                             (order-interval family b a)
                             (contains? (subdimembers family b) a)
                             (order-interval family a b)
                             :else #{})]
            :when (not= suborder #{})]
        suborder)))))

; Dependence and independence
(defn common-subdimembers
  [family a b]

  (intersection (subdimembers family a)
                (subdimembers family b)))

(defn common-superdimembers
  [family a b]

  (intersection (superdimembers family a)
                (superdimembers family b)))

(defn independent-dimembers
  [family]

  (let [dimembers (apply union family)
        is-unique-minima? (unique-minima-family? family)]
    (union
     (unary-family dimembers)
     (set
      (filter
       (fn [pair]
         (let [[a b] (seq pair)]
           (if is-unique-minima?
             (<= (count (common-subdimembers family a b)) 1)
             (= (count (common-subdimembers family a b)) 0))))
       (selections dimembers 2))))))

(defn dependent-dimembers
  [family]

  (let [dimembers (apply union family)
        is-unique-maxima? (unique-maxima-family? family)]
    (union
     (unary-family dimembers)
     (set
      (filter
       (fn [pair]
         (let [[a b] (seq pair)]
           (if is-unique-maxima?
             (<= (count (common-superdimembers family a b)) 1)
             (= (count (common-superdimembers family a b)) 0))))
       (selections dimembers 2))))))

(defn complementary-dimembers
  [family]

  (intersection
   (independent-dimembers family)
   (dependent-dimembers family)))

; Related containment families
(defn logical-containment
  [func coll]

  (set
   (map
    (fn [i]
      (let [current-elements (func i)]
        (set
         (filter
          (fn [j]
            (superset? (list (func j) current-elements)))
          coll))))
    coll)))

(defn underlying-containment
  [family]

  (set (map (partial subdimembers family) (apply union family))))

(defn transpose-containment
  [family]

  (set (map (partial superdimembers family) (apply union family))))

(defn adjacencies-containment
  [family]

  (logical-containment (partial adjacencies family) (apply union family)))

(defn neighbourhoods-containment
  [family]

  (logical-containment (partial neighbourhood family) (apply union family)))

; Preorder containment families
(defn subcontainment
  [family coll]

  (set
   (map
    (fn [i]
      (intersection coll (cl family #{i})))
    coll)))

(defn subcontainments
  [pred? family]

  (set
   (filter
    (fn [coll]
      (pred? (subcontainment family coll)))
    (power-set (apply union family)))))

(defn preorder-containment-family?
  [family]

  (= family (underlying-containment family)))

(def order-containment-family?
  (intersection
   preorder-containment-family?
   (comp unary-family? distinguishability)))

; Underlying chain
(defn underlying-chain
  [family]

  (letfn [(preceding-lower-set? [family coll]
            
            (let [remaining-elements (difference (apply union family) coll)]
              (every?
               (fn [parent]
                 (every?
                  (fn [j]
                    (contains? (subdimembers family parent) j))
                  coll))
               remaining-elements)))
          (acquire-lower-set [family n] 
            (if (= n (count (apply union family)))
              (apply union family)
              (let [current-lower-sets (filter
                                        (partial preceding-lower-set? family)
                                        (selections (apply union family) n))]
                (if (empty? current-lower-sets)
                  (acquire-lower-set family (inc n))
                  (first current-lower-sets)))))]
    (let [coll (apply union family)]
      (if (empty? coll)
        #{}
        (let [current-lower-set (acquire-lower-set family 1)]
          (union
           (set
            (map
             (fn [i]
               (union current-lower-set i))
             (underlying-chain
              (subcontainment
               family
               (set (difference coll current-lower-set))))))
           #{current-lower-set}))))))

; Weak order containment family
(defn weak-order-containment-family
  [colls]

  (if (empty? colls)
    #{}
    (union
     (unary-family (first colls))
     (set
      (map
       (fn [i]
         (union (first colls) i))
       (weak-order-containment-family (vec (rest colls))))))))

; Join representations
(defn join-representations
  [family]

  (subspace family (strongly-join-irreducible-dimembers family)))

(defn nullfree-join-representations
  [family]

  (subspace family (join-irreducible-dimembers family)))

(defn join-representations-family?
  [family]

  (and
   (order-containment-family? (set (filter (complement empty?) (union-irreducible-members family))))
   (every?
    (fn [pair]
      (or
       (contains? pair (apply intersection pair))
       (let [coll (suprema-members family pair)]
         (or
          (not= (count coll) 1)
          (let [current-coll (first coll)]
            (= current-coll               
               (apply
                union
                (filter
                 (fn [i]
                   (and
                     (not= i current-coll)
                     (superset? (list i current-coll))))
                 family))))))))
    (selections family 2))))

(defn fully-join-representations-family?
  [family]

  (and
   (join-representations-family? family)
   (or
    (empty? family)
    (empty? (apply intersection family)))))

(def nullfree-join-representations-family?
  (intersection
   nullfree-family?
   join-representations-family?))

; Adjacency families
(defn adjacencies-family
  [family]

  (set (map (partial adjacencies family) (apply union family))))

(defn order-connectivity-preserving-family?
  [family]

  (or
   (contains? family #{})
   (= (adjacency-connected-components family) (order-connected-components family))))

(defn adjacencies-family?
  [family]

  (every?
   (fn [coll]
     (or
      (= (count (apply union coll)) 1)
      (not
       (every?
        (complement
         (fn [i]
           (= (adjacencies-family i) coll)))
        (power-set (selections (apply union coll) 2))))))
   (adjacency-connected-components family)))

(defn augmentation-family?
  [family]

  (every?
   (fn [pair]
     (or
      (apply = (map count pair))
      (let [[a b] (sort (fn [i j] (< (count i) (count j))) pair)]
        (not
         (every?
          (complement
           (fn [i]
             (family (union #{i} a))))
          (difference b a))))))
   (selections family 2)))

(def kolmogorov-family?
  (intersection
   family-of-universals?
   (comp (power-set singular-universal?) distinguishability)))

(def nullfree-kolmogorov-family?
  (intersection
   nullfree-family?
   (comp (power-set singular-universal?) distinguishability)))

(defn subsingleton-maintaining-family?
  [family]

  (let [coll (apply union (intersection singular-universal? family))]
    (every?
     (fn [i]
       (or
        (empty? i)
        (not (empty? (intersection i coll)))))
     family)))

(def subsingleton-maintaining-kolmogorov-family?
  (intersection
   kolmogorov-family?
   subsingleton-maintaining-family?))

(defn cover-preserving-family?
  [family]

  (letfn [(covering-pair? [pair]
            (and
             (contains? pair (apply intersection pair))
             (let [a (apply intersection pair)
                   b (apply union pair)]
               (every?
                (fn [i]
                  (not
                    (and
                      (not= i a)
                      (not= i b)
                      (superset? (list a i))
                      (superset? (list i b)))))
                family))))]
    (every?
     (fn [pair]
       (or
        (not (covering-pair? pair))
        (= (inc (count (apply intersection pair)))
           (count (apply union pair)))))
     (selections family 2))))

(def semiaccessible-family?
  (intersection
   family-of-universals?
   (fn [family]
     (every?
      (fn [coll]
        (or
         (<= (count coll) 1)
         (not
          (every?
           (complement
            (fn [i]
              (contains? family (difference coll #{i}))))
           coll))))
      family))))

(def accessible-family?
  (intersection
   subnull-closed?
   semiaccessible-family?))

(def coaccessible-family?
  (comp accessible-family? complementary-family))

(def biaccessible-family?
  (intersection
   accessible-family?
   coaccessible-family?))

(def greedoid?
  (intersection
   accessible-family?
   augmentation-family?))

(def cogreedoid?
  (intersection
   coaccessible-family?
   augmentation-family?))

(def bigreedoid?
  (intersection
   biaccessible-family?
   augmentation-family?))

; Subclass related families
(def subnonnull-closed?
  (moore-family
   universal?
   (fn [coll]
     (let [subclass-closure (apply
                             union
                             (map
                              power-set
                              (maximal-members coll)))]
       (if (contains? coll #{})
         subclass-closure
         (disj subclass-closure #{}))))))

(def subnonsingleton-closed?
  (moore-family
   universal?
   (fn [coll]
     (let [subclass-closure (apply
                             union
                             (map
                              power-set
                              (maximal-members coll)))]
       (union
        coll
        (intersection (complement singular-universal?) subclass-closure))))))

(def subnonunique-closed?
  (moore-family
   universal?
   (fn [coll]
     (let [subclass-closure (apply
                             union
                             (map
                              power-set
                              (maximal-members coll)))]
       (union
        coll
        (intersection (complement (cardinality-classification #{0 1})) subclass-closure))))))

; Subclass closed families
(defn uniform-matroid
  [coll n]

  (multiselection coll (set (range (inc n)))))

(defn dual-matroid
  [family]

  (let [basis-sets (filter
                         (fn [i]
                           (and
                            (set? i)
                            (every?
                             (fn [j]
                               (or
                                (= i j)
                                (not (= i (intersection i j)))))
                             family)))
                         family)]
    (set
     (filter
      (fn [coll]
        (not
         (every?
          (complement
           (fn [i]
             (empty? (intersection i coll))))
          basis-sets)))
      (power-set (apply union family))))))

(defn necessary-rank
  [family]

  (letfn [(family-of-necessary-rank? [family n]          
            (let [specific-family (intersection family (fn [i] (<= (count i) n)))]
              (every?
               (fn [coll]
                 (let [current-family (subfamily specific-family coll)]
                   (if (and
                        (rank-complete-family? current-family)
                        (= (rank current-family) n))
                     (contains? family coll)
                     (not (contains? family coll)))))
               (multiselection (apply union family) (set (range (inc n) (inc (count family))))))))
          (get-necessary-rank [family n]
            (if (family-of-necessary-rank? family n)
              n
              (get-necessary-rank family (inc n))))]
    (get-necessary-rank family 1)))

(def subclass-closed?
  (moore-family
   universal?
   (fn [coll]
     (apply union (map power-set (maximal-members coll))))))

(def power-set?
  (moore-family
   universal?
   (fn [coll]
     (power-set (apply union coll)))))

(def clique-family?
  (moore-family
   universal?
   (fn [family]
     (if (empty? family)
       family
       (let [subclass-closed-family ((:closure subclass-closed?) family)
             underlying-coll (apply
                              union
                              (intersection
                               (selections entity? 1)
                               subclass-closed-family))
             unordered-tuples (intersection
                               (selections entity? 2)
                               subclass-closed-family)
             cliques (set
                      (filter
                       (fn [coll]
                         (or
                           (<= (count coll) 1)
                           (superset? (list (selections coll 2) unordered-tuples))))
                       (power-set underlying-coll)))]
         (union family cliques))))))

(def cluster-cliques-family?
  (moore-family
   universal?
   (fn [family]
     (apply
      union
      (map
       (fn [i]
         (power-set (apply union i)))
       (adjacency-connected-components family))))))

(def matroid?
  (intersection
   augmentation-family?
   subclass-closed?))

(def cocluster-cliques-family?
  (intersection
   clique-family?
   matroid?))

(def uniform-matroid?
  (moore-family
   universal?
   (fn [family]
     (if (empty? family)
       family
       (uniform-matroid
        (apply union family)
        (if (empty? family)
          0
          (apply max (map count family))))))))

; Superclass closed
(def superclass-closed?
  (moore-family
   universal?
   (fn [coll]
     (apply
      union
      (map
       (fn [elem]
         (fn [super-set]
           (= super-set (intersection super-set elem))))
       coll)))))

(def super-set?
  (moore-family
   universal?
   (fn [coll]
     (super-set (apply intersection coll)))))

; Extrema
(def union-closed?
  (moore-family
   universal?
   (fn [coll]
     (set
      (map
       (partial apply union)
       (disj (power-set coll) #{}))))))

(def intersection-closed?
  (moore-family
   universal?
   (fn [coll]
     (set
      (map
       (partial apply intersection)
       (disj (power-set coll) #{}))))))

(def extrema-closed?
  (moore-family
   universal?
   (comp (partial cl intersection-closed?) (partial cl union-closed?))))

; Dependent extrema
(def disjoint-union-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (if (not (empty? (apply intersection coll)))
            #{}
            #{(apply union coll)}))
        (disj (power-set family) #{})))))))

(def disjoint-intersection-closed?
  (moore-family
   universal?
   (fn [family]
     (if (antidisjoint-family? family)
       family
       (union #{#{}} family)))))

(def disjoint-extrema-closed?
  (moore-family
   universal?
   (fn [family]
     (cl disjoint-intersection-closed? (cl disjoint-union-closed? family)))))

(def nondisjoint-union-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (if (empty? (apply intersection coll))
            #{}
            #{(apply union coll)}))
        (disj (power-set family) #{})))))))

(def nondisjoint-intersection-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (if (empty? (apply intersection coll))
            #{}
            #{(apply intersection coll)}))
        (disj (power-set family) #{})))))))

(def nondisjoint-extrema-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (if (empty? (apply intersection coll))
            #{}
            (set
             (list
              (apply intersection coll)
              (apply union coll)))))
        (disj (power-set family) #{})))))))

; Subclass difference closed
(def subclass-difference-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (set
       (for [pair (selections family 2)
             :when (contains? pair (apply intersection pair))]
         (difference
          (apply union pair)
          (apply intersection pair))))))))

(def difference-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (if (empty? family) #{} #{#{}})
      (apply
       union
       (map
        (fn [pair]
          (let [[a b] (seq pair)]
            (set
             (list
              (difference a b)
              (difference b a)))))
        (selections family 2)))))))

; Symmetric difference closed
(def symmetric-difference-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (if (empty? family) #{} #{#{}})
      (set
       (map
        (fn [coll]
          (apply symmetric-difference coll))
        (disj (power-set family) #{})))))))

; Classes of convex families
(def convex-family?
  (moore-family
   universal?
   (fn [coll]
     (apply
      union
      (cons
       coll
       (map
        (fn [pair]
          (if (contains? pair (apply intersection pair))
            (logical-interval (apply intersection pair) (apply union pair))
            #{}))
        (selections coll 2)))))))

(def uniquely-connected-convex-family?
  (intersection
   convex-family?
   uniquely-connected-family?))

(def unique-minima-convex-family?
  (moore-family
   universal?
   (fn [coll]
     (cl convex-family? (union #{(apply intersection coll)} coll)))))

(def unique-maxima-convex-family?
  (moore-family
   universal?
   (fn [coll]
     (cl convex-family? (union #{(apply union coll)} coll)))))

(def logical-interval?
  (moore-family
   universal?
   (fn [coll]
     (logical-interval (apply intersection coll) (apply union coll)))))

(def rank-complete-convex-family?
  (moore-family
   universal?
   (fn [family]
     (if (empty? family)
       family
       (let [coll (apply union family)
             counts (set (map count family))
             min-count (apply min counts)
             max-count (apply max counts)]
         (multiselection coll (set (range min-count (inc max-count)))))))))

; Image equivalence classes are also convex families
(defn image-equivalence-class?
  [family]

  (and
   (unique-maxima-convex-family? family)
   (cocluster-maximal-cliques-family? (minimal-members family))))

; Extrema closed families
(def product-family
  (letfn [(product [first-family second-family]
            (apply
             union
             (map
              (fn [i]
                (set
                 (map
                  (fn [j]
                    (union i j))
                  second-family)))
              first-family)))]
    (fn
      ([] #{})
      ([a] a)
      ([a b] (product a b))
      ([a b & more] (reduce product (product a b) more)))))

(defn alexandrov-connectivity
  [family]

  (letfn [(removable-set? [family elems]
            (let [remaining-elems (difference (apply union family) elems)]
              (= family
                 (product-family
                  (subspace family elems)
                  (subspace family remaining-elems)))))
          (find-removable-sets [family coll n]
            (cond
             (empty? coll) #{}
             (< (int (/ (count coll) 2)) n) #{coll}
             :else (let [current-removable-sets (set
                                                 (filter
                                                  (partial removable-set? family)
                                                  (selections coll n)))
                         removable-elements (apply union current-removable-sets)]
                     (union
                      current-removable-sets
                      (find-removable-sets
                       family
                       (difference coll removable-elements)
                       (inc n))))))]
    (find-removable-sets family (apply union family) 1)))

(def cover-preserving-extrema-closed-family?
  (intersection
   cover-preserving-family?
   extrema-closed?))

(def kolmogorov-extrema-closed-family?
  (intersection
   kolmogorov-family?
   extrema-closed?))

(def alexandrov-family?
  (moore-family
   universal?
   (fn [coll]
     (union #{#{}} (cl extrema-closed? coll)))))

(def order-complex?
  (intersection
   alexandrov-family?
   (comp unary-family? distinguishability)))

(def partition-family?
  (moore-family
   universal?
   (comp (partial union #{#{}}) (partial cl extrema-closed?) distinguishability)))

(defn excluded-point-family?
  [family]

  (let [a (apply union (intersection singular-universal? family))
        b (apply union family)]
    (or
     (and
      (= a b)
      (<= (count family) 2)
      (= family (power-set a)))
     (and
      (= (count a) (dec (count b)))
      (= family (union (power-set a) #{b}))))))

(defn included-point-family?
  [family]

  (let [a (apply union (intersection singular-universal? family))
        b (apply union family)]
    (and
     (or
      (= (count b) 0)
      (= (count a) 1))
     (= family (union #{#{}} (logical-interval a b))))))

; Moore families
(defn moore-completion
  [family]

  (union
   (cl intersection-closed? family)
   #{(apply union family)}))

(defn moore-generators
  [family elem]

  (set
   (filter
    (fn [i]
      (= (cl family i) elem))
    (power-set elem))))

(defn minimal-moore-generators
  [family elem]
  
  (let [current-generators (moore-generators family elem)]
    (set
     (filter
      (fn [current-generator]
        (every?
         (fn [i]
           (or
             (= current-generator i)
             (not (superset? (list i current-generator)))))
         current-generators))
      current-generators))))

(defn moore-bases
  [family]

  (minimal-moore-generators family (apply union family)))

(defn moore-dimension
  [family]

  (corank (moore-bases family)))

(defn moore-independent-sets
  [family]

  (apply
   union
   (map
    (partial minimal-moore-generators family)
    family)))

(defn closed-independent-sets
  "Sometimes sets can generate themselves."
  [family]

  (intersection
    family
    (moore-generators family (apply union family))))

(defn matroid-flats
  [matroid]

  (letfn [(flat? [family coll]
            (= coll
               (set
                (filter
                 (fn [i]
                   (= (rank (subfamily family coll))
                      (rank (subfamily family (union coll #{i})))))
                 (apply union family)))))]
    (set
     (filter
      (partial flat? matroid)
      (power-set (apply union matroid))))))

(def moore-family?
  (intersection
   intersection-closed?
   (fn [family]
     (or
      (empty? family)
      (contains? family (apply union family))))))

(defn matroid-moore-family?
  [family]

  (and
   (moore-family? family)
   (= family (matroid-flats (subspaces power-set? family)))))

(def cover-preserving-moore-family?
  (intersection
   moore-family?
   cover-preserving-family?))

(def kolmogorov-moore-family?
  (intersection
   moore-family?
   (comp unary-family? distinguishability)))

(def rank-complete-moore-family?
  (intersection
   rank-complete-family?
   moore-family?))

(def atomistic-moore-family?
  (intersection
   moore-family?
   subsingleton-closed?))

(def accessible-moore-family?
  (intersection
   moore-family?
   accessible-family?))

(def convex-geometry?
  (intersection
   moore-family?
   (comp accessible-family? complementary-family)))

(def atomistic-convex-geometry?
  (intersection
   subsingleton-closed?
   convex-geometry?))

; Comoore families
(defn comoore-completion
  [family]

  (union
   (cl union-closed? family)
   #{(apply intersection family)}))

(def comoore-family?
  (intersection
   union-closed?
   (fn [family]
     (or
      (empty? family)
      (contains? family (apply intersection family))))))

(def cover-preserving-comoore-family?
  (intersection
   cover-preserving-family?
   comoore-family?))

(def kolmogorov-comoore-family?
  (intersection
   kolmogorov-family?
   comoore-family?))

(def rank-complete-comoore-family?
  (intersection
   rank-complete-family?
   comoore-family?))

(def coatomistic-comoore-family?
  (comp atomistic-moore-family? complementary-family))

(def coaccessible-comoore-family?
  (intersection
   coaccessible-family?
   comoore-family?))

(def antimatroid?
  (intersection
   accessible-family?
   union-closed?))

(def coatomistic-antimatroid?
  (intersection
   antimatroid?
   (comp subsingleton-closed? complementary-family)))

; Nondisjoint union closed families
(def connectivity-complex?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      #{#{}}
      (selections (apply union family) 1)
      (set
       (for [subfamily (power-set family)
             :when (and
                    (not (empty? subfamily))
                    (uniquely-dependent-family? subfamily))]
         (apply union subfamily)))))))

(defn dependency-generated-connectivity-complex?
  [family]

  (let [dependency-part (cl
                         subsingleton-closed?
                         (intersection
                          (multiselection entity? #{1 2})
                          family))]
    (= family (cl connectivity-complex? dependency-part))))

; Common point closed
(def common-point-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (let [minima (minimal-members coll)
                maxima (maximal-members coll)]
            (if (not= (count minima) (count maxima) 2)
              #{}
              (let [[a b] (seq minima)
                    [c d] (seq maxima)]
                (if (and
                      (superset? (list a c))
                      (superset? (list a d))
                      (superset? (list b c))
                      (superset? (list b d)))
                  (logical-interval (union a b) (intersection c d))
                  #{})))))
        (selections family 4)))))))

(def lower-common-point-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (let [minima (minimal-members coll)
                maxima (maximal-members coll)]
            (if (not (and (= (count minima) 2)
                          (= (count maxima) 1)))
              #{}
              (let [[a b] (seq minima)
                    [c] (seq maxima)]
                (if (and
                      (superset? (list a c))
                      (superset? (list b c)))
                  (logical-interval (union a b) c)
                  #{})))))
        (selections family 3)))))))

(def upper-common-point-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (let [minima (minimal-members coll)
                maxima (maximal-members coll)]
            (if (not (and (= (count minima) 1)
                          (= (count maxima) 2)))
              #{}
              (let [[a] (seq minima)
                    [b c] (seq maxima)]
                (if (and
                      (superset? (list a b))
                      (superset? (list a c)))
                  (logical-interval a (intersection b c))
                  #{})))))
        (selections family 3)))))))

(def semicommon-point-closed?
  (moore-family
   universal?
   (fn [family]
     (union
      family
      (apply
       union
       (map
        (fn [coll]
          (let [minima (minimal-members coll)
                maxima (maximal-members coll)]
            (if (or (and (= (count minima) 2)
                         (= (count maxima) 1))
                    (and (= (count minima) 1)
                         (= (count maxima) 2)))
              (logical-interval (apply union minima) (apply intersection maxima))
              #{})))
        (selections family 3)))))))

; Common extrema closed
(def common-extrema-closed?
  (moore-family
   universal?
   (fn [family]
     (intersection
      (cl union-closed? family)
      (cl intersection-closed? family)))))

(def subunion-closed?
  (moore-family
   universal?
   (fn [coll]
     (union
      coll
      (apply
       union
       (map
        (fn [i]
          (let [current-union (apply union i)]
            (if (not
                 (every?
                  (complement
                    (fn [current-elem]
                     (superset? (list current-union current-elem))))
                  coll))
              #{current-union}
              #{})))
        (disj (power-set coll) #{})))))))

(def superintersection-closed?
  (moore-family
   universal?
   (fn [coll]
     (union
      coll
      (apply
       union
       (map
        (fn [i]
          (let [current-intersection (apply intersection i)]
            (if (not
                 (every?
                  (complement
                    (fn [current-elem]
                     (superset? (list current-elem current-intersection))))
                  coll))
              #{current-intersection}
              #{})))
        (disj (power-set coll) #{})))))))

(def semicommon-extrema-closed?
  (moore-family
   universal?
   (fn [coll]
     (union (cl subunion-closed? coll) (cl superintersection-closed? coll)))))

; Localized extrema
(def subextrema-closed?
  (moore-family
   universal?
   (fn [coll]
     (union (cl intersection-closed? coll) (cl subunion-closed? coll)))))

(def superextrema-closed?
  (moore-family
   universal?
   (fn [coll]
     (union (cl union-closed? coll) (cl superintersection-closed? coll)))))

; Path intervals family
(defn path-intervals-family?
  [family]

  (let [coll (set (filter (cardinality-classification #{1 2}) family))]
    (and
     (path-dependency-family? coll)
     (= family (metric-intervals coll)))))

; Intersection closed families
; Classification of intersection closed families by their maximal members
(defn sperner-intersections-family?
  [family]

  (and
   (sperner-family? (maximal-members family))
   (intersection-closed? family)))

(defn maximal-cliques-interesctions-family?
  [family]

  (and
   (maximal-cliques-family? (maximal-members family))
   (intersection-closed? family)))

(defn maximal-cliques-intersection-family
  [family]

  (cl intersection-closed? (maximal-cliques family)))

; Lagrange families emerge from set systems produced by subgroup lattices
; they are families of sets for which every comparable pair of sets the
; cardinality of the smaller set divides the cardinality of the larger one.
(defn lagrange-family?
  [coll]

  (every?
   (fn [pair]
     (let [[a b] (seq pair)]
       (cond
         (superset? (list a b)) (divides? (list (count a) (count b)))
         (superset? (list b a)) (divides? (list (count b) (count a)))
         :else true)))
   (selections coll 2)))

(def lagrange-chain-family?
  (intersection
   chain-family?
   lagrange-family?))

(defn complete-lagrange-family?
  [coll]

  (= coll
     (complete-lagrange-family (apply union coll))))

; Visualization
(defn specialization-covering
  [family]

  (union
   (set
    (map
     (fn [i]
       (list i i))
     (apply union (isolated-members family))))
   (set
    (map
     (fn [pair]
       (let [[a b] (seq pair)]
         (if (superset? (list (cl family #{a}) (cl family #{b})))
           (list a b)
           (list b a))))
     (intersection size-two-universal? (covering-pairs family))))))

(defn family-covering
  [family]

  (mapcat
   (fn [i]
     (let [n (count i)]
       (for [pred family
             :let [pred-size (count pred)]
             :when (and (< pred-size n)
                        (superset? (list pred i))
                        (every?
                         (fn [middle]
                           (not
                             (and (not= middle i)
                                  (not= middle pred)
                                  (superset? (list pred middle))
                                  (superset? (list middle i)))))
                         family))]
         (list pred i))))
   family))
