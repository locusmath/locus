package locus.ui.quiver.edge;

import locus.ui.quiver.line.LineFactory;
import javafx.geometry.Point2D;
import javafx.scene.shape.Line;
import javafx.scene.shape.Rectangle;

public class VertexConnector {
    public static Point2D rectangleCenter(Rectangle rect) {
        return new Point2D(rect.getX()+rect.getWidth()/2, rect.getY()+rect.getHeight()/2);
    }

    public static Line rectangleConnector(Rectangle rect1, Rectangle rect2) {
        var c1 = rectangleCenter(rect1);
        var c2 = rectangleCenter(rect2);
        var currentLine = LineFactory.makeLine(c1,c2);
        var p1 = currentLine.getNearestIntersection(rect1, c2);
        var p2 = currentLine.getNearestIntersection(rect2, c1);
        return new Line(p1.getX(), p1.getY(), p2.getX(), p2.getY());
    }

}
