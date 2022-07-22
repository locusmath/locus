package locus.ui.quiver.vertex;

import javafx.scene.shape.Rectangle;

public class VertexData {
    public String label;
    public Rectangle bounds;

    public VertexData(String label, Rectangle bounds) {
        this.label = label;
        this.bounds = bounds;
    }

    public VertexNode toVertexNode() {
        return VertexNode.makeVertexNode(this.label, this.bounds);
    }
}
