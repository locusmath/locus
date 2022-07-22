package locus.ui.quiver.vertex;

import javafx.geometry.VPos;
import javafx.scene.Group;
import javafx.scene.paint.Color;
import javafx.scene.shape.Rectangle;
import javafx.scene.text.Text;
import javafx.scene.text.TextAlignment;

public class VertexNode extends Group {
    Rectangle rectangle;
    Text text;

    public VertexNode(Text currentText, double width, double height) {
        currentText.setTextOrigin(VPos.CENTER);
        currentText.setClip(new Rectangle(0, -height/2, width, height));
        currentText.setTextAlignment(TextAlignment.CENTER);
        currentText.setWrappingWidth(width);
        this.text = currentText;

        var newRectangle = new Rectangle(width, height);
        newRectangle.setFill(Color.rgb(240, 240, 240));
        newRectangle.setStroke(Color.BLACK);
        this.rectangle = newRectangle;

        this.getChildren().addAll(newRectangle, currentText);
        this.setOnMouseEntered((i) -> {
            newRectangle.setStroke(Color.RED);
            currentText.setFill(Color.RED);
        });
        this.setOnMouseExited((i) -> {
            newRectangle.setStroke(Color.BLACK);
            currentText.setFill(Color.BLACK);
        });
    }

    public VertexNode(String str, double width, double height) {
        this(new Text(str), width, height);
    }

    @Override
    protected void layoutChildren() {
        var width = rectangle.getWidth();
        var height = rectangle.getHeight();
        var textWidth = text.getLayoutBounds().getWidth();
        text.setLayoutX(width / 2 - textWidth / 2);
        text.setLayoutY(height / 2);
    }

    public static VertexNode makeVertexNode(String str, Rectangle rect) {
        var rval = new VertexNode(str, rect.getWidth(), rect.getHeight());
        rval.setLayoutX(rect.getX());
        rval.setLayoutY(rect.getY());
        return rval;
    }

}
