package locus.ui.quiver.edge;

import javafx.geometry.Point2D;
import javafx.scene.paint.Color;
import javafx.scene.shape.LineTo;
import javafx.scene.shape.MoveTo;
import javafx.scene.shape.Path;

public class ArrowHeadMaker {
    public static Path makeArrowHead(Point2D p1, Point2D p2, Point2D p3) {
        var rval = new Path();
        rval.getElements().add(new MoveTo(p1.getX(), p1.getY()));
        rval.getElements().add(new LineTo(p2.getX(), p2.getY()));
        rval.getElements().add(new LineTo(p3.getX(), p3.getY()));
        rval.setFill(Color.BLACK);
        return rval;
    }

}
