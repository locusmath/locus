package locus.ui.quiver.hom;
import locus.ui.quiver.edge.EdgeMaker;
import locus.ui.quiver.edge.RectangleRotator;
import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.shape.Line;
import javafx.scene.shape.Rectangle;

import java.util.Hashtable;

public class HomMaker {

    public static Object[][] getHomClassesByPartition(Object[][] edges, Integer[][] partition) {
        var rval = new Object[partition.length][4];

        for(int i = 0; i < partition.length; i++) {
            Integer[] part = partition[i];
            var firstEdge = edges[part[0]];

            var start = firstEdge[1];
            var end = firstEdge[2];
            String[] labels = new String[part.length];
            boolean[] directions = new boolean[part.length];

            for(int j = 0; j < part.length; j++) {
                var edgeLocation = part[j];
                var currentEdge = edges[edgeLocation];
                labels[j] = currentEdge[0].toString();
                directions[j] = start.equals(currentEdge[1]);
            }

            rval[i] = new Object[]{start, end, labels, directions};
        }

        return rval;
    }

    // public static getoffsets
    public static double[] getOffsets(int len) {
        var rval = new double[len];

        if(len == 1) {
            rval[0] = 0.0;
            return rval;
        }

        var size = (len >= 5) ? 1.0 : len*0.2;
        double offset = size/(len-1);

        for(int i = 0; i < len; i++) {
            rval[i] = offset* i - (size/2);
        }

        return rval;
    }

    public static Group makeHomClass(Point2D start, Point2D end, Rectangle source, Rectangle target, String[] labels, boolean[] directions, Hashtable<Object, Group> table) {
        var startFactor = RectangleRotator.getRectangleFactor(source, start);
        var endFactor = RectangleRotator.getRectangleFactor(target, end);

        var rval = new Group();
        var len = labels.length;
        var offsets = getOffsets(len);

        var mainFactor = (0.25)/len;

        for (int i = 0; i < len; i++) {
            var newOffset = mainFactor*i;
            var newStart = RectangleRotator.getRectangleCoordinate(source, startFactor + newOffset);
            var newEnd = RectangleRotator.getRectangleCoordinate(target, endFactor - newOffset);

            var currentLabel = labels[i];
            var currentEdge = (directions[i]) ?
                    EdgeMaker.makeEdge(newStart, newEnd, offsets[i], currentLabel) :
                    EdgeMaker.makeEdge(newEnd, newStart, offsets[i], currentLabel);

            table.put(currentLabel, currentEdge);
            rval.getChildren().add(currentEdge);
        }

        return rval;
    }

    public static Group makeHomClass(Point2D start, Point2D end, String[] labels, boolean[] directions) {
        var rval = new Group();
        var len = labels.length;
        var offsets = getOffsets(len);

        for (int i = 0; i < len; i++) {
            var currentEdge = (directions[i]) ?
                    EdgeMaker.makeEdge(start, end, offsets[i], labels[i]) :
                    EdgeMaker.makeEdge(end, start, offsets[i], labels[i]);

            rval.getChildren().add(currentEdge);
        }

        return rval;
    }

    public static Group makeHomClass(Line line, String[] labels, boolean[] directions) {
        var start = new Point2D(line.getStartX(), line.getStartY());
        var end = new Point2D(line.getEndX(), line.getEndY());
        return makeHomClass(start,end,labels, directions);
    }

}
