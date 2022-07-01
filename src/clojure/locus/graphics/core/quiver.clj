(ns locus.graphics.core.quiver
  (:require [locus.elementary.logic.base.core :refer :all]
            [locus.elementary.relation.binary.sr :refer :all]
            [locus.elementary.relation.binary.br :refer :all]
            [locus.elementary.incidence.system.family :refer :all]
            [locus.elementary.incidence.system.clan :refer :all]
            [locus.elementary.function.core.object :refer :all]
            [locus.elementary.function.core.protocols :refer :all]
            [locus.elementary.diamond.core.object :refer :all]
            [locus.elementary.quiver.core.object :refer :all]
            [locus.elementary.category.core.morphism :refer :all]
            [locus.elementary.topoi.copresheaf.object :refer :all]
            [locus.elementary.topoi.nset.object :refer :all]
            [locus.elementary.topoi.nset.morphism :refer :all]
            [locus.elementary.bijection.core.object :refer :all]
            [locus.elementary.diset.core.object :refer :all]
            [locus.elementary.action.global.object :refer :all]
            [locus.elementary.category.core.object :refer :all]
            [locus.elementary.category.core.generated-category :refer :all]
            [locus.elementary.groupoid.core.object :refer :all]
            [locus.elementary.group.core.object :refer :all]
            [locus.elementary.semigroup.core.object :refer :all]
            [locus.elementary.lattice.core.object :refer :all]
            [locus.elementary.order.core.poset :refer :all]
            [locus.elementary.quiver.dependency.object :refer :all]
            [locus.elementary.quiver.permutable.object :refer :all]
            [locus.elementary.quiver.unital.object :refer :all]
            [locus.elementary.incidence.core.object :refer :all]

    ;[locus.hypergraph.core.object :refer :all]
    ;[locus.graph.undirected.object :refer :all]
    ;[locus.hypergraph.incidence.incidence-structure :refer :all]
    ;[locus.elementary.topoi.copresheaf.algebraic :refer :all]
    ;[locus.algebra.magma.object :refer :all]
    ;[locus.algebra.partial-magma.object :refer :all]
    ;[locus.algebra.pointed-set.object :refer :all]
    ;[locus.semiring.core.object :refer :all]
            )
  (:import (javax.swing JFrame JLabel ImageIcon JPanel JButton JList JScrollPane JSplitPane SwingConstants CellRendererPane ListCellRenderer UIManager)
           (java.awt GridLayout Color Dimension FlowLayout RenderingHints BasicStroke Toolkit Image)
           (javax.swing.event ListSelectionListener)
           (java.awt.event MouseAdapter ComponentEvent MouseEvent ComponentAdapter)
           (locus.elementary.topoi.copresheaf.object Copresheaf)
           (locus.elementary.diamond.core.object Diamond)
           (java.util ArrayList)
           (java.awt.image BufferedImage)
           (java.awt.geom GeneralPath)
           (java.io ByteArrayInputStream)
           (javax.imageio ImageIO)))

(require '[dorothy.core :as dot])
(require '[dorothy.jvm :refer (render save! show!)])

; This file essentially implements the copresheaf viewer, which is one of the fundamental
; objects of Locus. It allows us to interact visually with the most basic objects of
; the Locus computer algebra system, which are presheaves over finitely generated categories.

(defn create-vertices
  [quiver vertex-labels]

  (vec
    (map
      (fn [i]
        [(.toString i) {:label (vertex-labels i)}])
      (objects quiver))))

(defn create-edges
  [quiver edge-labels]

  (vec
    (map
      (fn [edge]
        [(.toString (source-element quiver edge))
         (.toString (target-element quiver edge))
         {:label (str " " (edge-labels edge) " ")}])
      (morphisms quiver))))

(defn create-edges-unlabeled
  [quiver]

  (vec
    (map
      (fn [edge]
        [(.toString (source-element quiver edge))
         (.toString (target-element quiver edge))
         {:label ""}])
      (morphisms quiver))))

(defn dot-quiver
  ([quiver]
   (dot-quiver quiver #(.toString %) #(.toString %)))
  ([quiver vertex-labels edge-labels]
   (dot/digraph
     (vec
       (concat
         (list [{:rankdir "LR"}])
         (create-vertices quiver vertex-labels)
         (create-edges quiver edge-labels))))))

(defn dot-function
  [func]

  (let [rel (underlying-relation func)
        quiver (relational-quiver rel)]
    (dot/digraph
      (vec
        (concat
          (list [{:rankdir "BT"}])
          (create-vertices quiver #(.toString %))
          (create-edges-unlabeled quiver))))))

(defn display-dot-function
  [title func]

  (let [frame (JFrame.)
        ^bytes bytes (-> (dot-function func) dot/dot (render {:format :png}))
        icon (ImageIcon. bytes)
        label (JLabel. icon)]
    (.add frame label)
    (.setVisible frame true)
    (.setLocationRelativeTo frame nil)
    (.setTitle frame title)
    (.setSize
      frame
      (+ 50 (* 7 (.length (.getTitle frame))) (.getIconWidth icon))
      (+ 10 (.-top (.getInsets frame)) (.getIconHeight icon)))))

(defmethod visualize Diamond
  [func] (visualize (to-copresheaf func)))

; node and arrow images for the copresheaf viewer
(defn ^BufferedImage node-image
  []

  (let [rval (new BufferedImage 30 30 BufferedImage/TYPE_INT_ARGB)
        g (.createGraphics rval)]

    ; do the graphics processing

    (.setRenderingHint g RenderingHints/KEY_ANTIALIASING RenderingHints/VALUE_ANTIALIAS_ON)
    (.setColor g Color/BLACK)
    (.drawOval g 8 8 14 14)

    ; return the image
    rval))

(defn ^BufferedImage arrow-image
  []

  (let [rval (new BufferedImage 30 30 BufferedImage/TYPE_INT_ARGB)
        g (.createGraphics rval)]

    ; do the graphics processing

    (.setRenderingHint g RenderingHints/KEY_ANTIALIASING RenderingHints/VALUE_ANTIALIAS_ON)
    (.setColor g Color/BLACK)
    (.setStroke g (new BasicStroke 1.5))
    (.drawLine g 4 15 26 15)

    (let [^GeneralPath p (GeneralPath.)]
      (.moveTo p 26.0 15.0)
      (.lineTo p 21.0 10.0)
      (.lineTo p 21.0 20.0)
      (.lineTo p 26.0 15.0)
      (.fill g p))

    ; return the image
    rval))

(defn ^BufferedImage resize-image
  [img width height]

  (let [rval (BufferedImage. width height BufferedImage/TRANSLUCENT)
        g (.createGraphics rval)]
    ; do the graphics processing
    (doto g
      (.setRenderingHints (RenderingHints. RenderingHints/KEY_RENDERING RenderingHints/VALUE_RENDER_QUALITY))
      (.drawImage img 0 0 width height nil))
    (.dispose g)

    ; return the image
    rval))

(defn properly-resize-image
  [img width height]

  (let [aspect-ratio (/ (.getWidth img)
                        (.getHeight img))
        chosen-height (/ width aspect-ratio)]
    (resize-image img width chosen-height)))

(defn ^BufferedImage make-image-by-bytes
  [^bytes coll]

  (let [bais (ByteArrayInputStream. coll)]
    (ImageIO/read bais)))

(defmethod visualize Copresheaf
  [copresheaf]

  (let [frame (JFrame.)
        main-panel (JPanel.)
        source-category (.category copresheaf)
        quiv (morphically-generated-subquiver source-category)
        ^bytes bytes (-> (dot-quiver quiv) dot/dot (render {:format :png}))
        img (make-image-by-bytes bytes)
        icon (ImageIcon. img)
        label (JLabel. icon)
        objects-collection (seq (objects quiv))
        morphisms-collection (seq (morphisms quiv))
        image-view-panel (JPanel. (new GridLayout 1 1))
        selection-panel (JPanel. (new GridLayout 1 1))
        split-pane (JSplitPane. SwingConstants/VERTICAL image-view-panel selection-panel)
        list (JList.)
        panels (ArrayList.)
        arrow-icon (ImageIcon. (arrow-image))
        node-icon (ImageIcon. (node-image))]

    ; set up the list
    (doseq [obj objects-collection]
      (let [current-panel (JPanel. (new FlowLayout FlowLayout/LEFT))]
        (.putClientProperty current-panel "isObject" true)
        (.putClientProperty current-panel "id" (.toString obj))
        (.add current-panel (new JLabel (.toString obj) node-icon JLabel/LEFT))
        (.add panels current-panel)))

    (doseq [morphism morphisms-collection]
      (let [current-panel (JPanel. (new FlowLayout FlowLayout/LEFT))]
        (.putClientProperty current-panel "isObject" false)
        (.putClientProperty current-panel "id" (.toString morphism))
        (.add current-panel (new JLabel (.toString morphism) arrow-icon JLabel/LEFT))
        (.add panels current-panel)))

    (.setCellRenderer
      list
      (proxy [ListCellRenderer] []
        (getListCellRendererComponent [jlist component i b1 b2]
          (.setForeground component Color/WHITE)
          (.setBackground
            component
            (if b1 (UIManager/getColor "Button.focus") Color/WHITE))
          component)))
    (.setListData list (into-array Object panels))

    (.addMouseListener
      list
      (proxy [MouseAdapter] []
        (mouseClicked [^MouseEvent e]
          (let [v (.getSelectedValue list)]
            (when (not (nil? v))
              (let [object? (boolean (.getClientProperty v "isObject"))
                    elem (.getClientProperty v "id")]
                (if object?
                  (visualize
                    (identity-function (object-apply copresheaf elem)))
                  (visualize
                    (morphism-apply copresheaf elem)))))))))

    (.add selection-panel (JScrollPane. list))

    ; set up the image view panel
    (.addComponentListener
      image-view-panel
      (proxy [ComponentAdapter] []
        (componentResized [^ComponentEvent e]
          (let [component (.getComponent e)
                width (.getWidth component)
                height (.getHeight component)]
            (when (not (or (<= width 0)
                           (<= height 0)))
              (let [new-image (properly-resize-image img width height)
                    new-icon (ImageIcon. new-image)]
                (.setIcon label new-icon)))))))

    (.add image-view-panel label)
    (.setMinimumSize image-view-panel (Dimension. 0 0))

    ; set up the split pane
    (.add main-panel split-pane)
    (.setLayout main-panel (new GridLayout 1 1))
    (.setResizeWeight split-pane (double 1))

    ; display the main frame
    (.setContentPane frame main-panel)
    (.setVisible frame true)
    (.setSize
      frame
      (+ 100 (.getWidth list) (.getIconWidth icon))
      (+ 10 (.getHeight list) (.-top (.getInsets frame)) (.getIconHeight icon)))
    (.setLocationRelativeTo frame nil)
    (.setTitle frame "Copresheaf viewer")))

