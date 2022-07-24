package locus.ui.quiver.hom;

import locus.ui.quiver.edge.EdgeMaker;
import locus.ui.quiver.edge.RectangleRotator;
import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.shape.Rectangle;

import java.util.Hashtable;

public class LoopMaker {

    public static Group makeLoop(Rectangle myRect, double start, double end, String label) {
        var coord1 = RectangleRotator.getRectangleCoordinate(myRect, start);
        var coord2 = RectangleRotator.getRectangleCoordinate(myRect,end);

        var rectangleCenter = new Point2D(myRect.getX() + myRect.getWidth()/2, myRect.getY() + myRect.getHeight()/2);

        var midpoint1 = EdgeMaker.getMidpoint(coord1, coord2, 0.5);
        var midpoint2 = EdgeMaker.getMidpoint(coord1, coord2, -0.5);
        var firstLarger = (midpoint1.distance(rectangleCenter) > midpoint2.distance(rectangleCenter));
        var preferredFactor = firstLarger ? 0.5 : -0.5;
        var edge = EdgeMaker.makeEdge(coord1, coord2, preferredFactor, label);
        return edge;
    }

    public static Group makeLoopClass(Rectangle myRect, Object[] ids, String[] labels, Hashtable<Object, Group> table) {
        var len = labels.length;
        var offsetFactor = (len > 4) ? 1.0/len : 0.25;
        var rval = new Group();

        for(var i = 0; i < len; i++) {
            var currentId = ids[i];
            var currentLabel = labels[i];
            var currentLoop = makeLoop(myRect, offsetFactor*i, offsetFactor*(i+1), currentLabel);

            table.put(currentId, currentLoop);
            rval.getChildren().add(currentLoop);
        }

        return rval;
    }

}
