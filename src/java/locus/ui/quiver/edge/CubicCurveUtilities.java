package locus.ui.quiver.edge;

import javafx.geometry.Point2D;
import javafx.scene.shape.CubicCurve;

public class CubicCurveUtilities {
    public static CubicCurve quadraticCubicCurve(Point2D p1, Point2D c, Point2D p2) {
        var c1 = new Point2D(
                (float) 2/3*c.getX() + (float) 1/3 * p1.getX(),
                (float) 2/3*c.getY() + (float) 1/3 * p1.getY()
        );
        var c2 = new Point2D(
                (float) 2/3*c.getX() + (float) 1/3 * p2.getX(),
                (float) 2/3*c.getY() + (float) 1/3 * p2.getY()
        );

        return new CubicCurve(p1.getX(), p1.getY(), c1.getX(), c1.getY(), c2.getX(), c2.getY(), p2.getX(), p2.getY());
    }
}
