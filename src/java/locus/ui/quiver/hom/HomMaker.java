package locus.ui.quiver.hom;
import locus.ui.quiver.edge.EdgeMaker;
import locus.ui.quiver.edge.RectangleRotator;
import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.shape.Line;
import javafx.scene.shape.Rectangle;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.function.BiPredicate;

public class HomMaker {

    public static ArrayList<ArrayList<Integer>> partition(Object[] coll, BiPredicate<Object, Object> comparator) {
        var rval = new ArrayList<ArrayList<Integer>>();
        var seenValues = new ArrayList<Object>();

        for(int i = 0, l = coll.length; i < l; i++) {
            var currentValue = coll[i];

            var currentIndex = -1;
            for(int j = 0; j < seenValues.size(); j++) {
                if(comparator.test(seenValues.get(j), currentValue)) {
                    currentIndex = j;
                    break;
                }
            }

            if(currentIndex == -1) {
                seenValues.add(currentValue);
                var currentArrayList = new ArrayList<Integer>();
                currentArrayList.add(i);
                rval.add(currentArrayList);
            } else {
                rval.get(currentIndex).add(i);
            }

        }

        return rval;
    }

    public static ArrayList<ArrayList<Integer>> partition(EdgeData[] coll) {
        return partition(coll, (x,y) -> ((EdgeData) x).isSimilarTo((EdgeData) y));
    }

    public static Object[][] getHomClasses(EdgeData[] edges) {
        return getHomClassesByPartition(edges, partition(edges));
    }

    public static Object[][] getHomClassesByPartition(EdgeData[] edges, ArrayList<ArrayList<Integer>> partition) {
        var len = partition.size();
        var rval = new Object[len][4];

        for(int i = 0; i < len; i++) {
            var part = partition.get(i);
            var partLength = part.size();

            var firstEdge = edges[part.get(0)];

            var start = firstEdge.source;
            var end = firstEdge.target;

            String[] labels = new String[partLength];
            boolean[] directions = new boolean[partLength];

            for(int j = 0; j < partLength; j++) {
                var edgeLocation = part.get(j);
                var currentEdge = edges[edgeLocation];

                labels[j] = currentEdge.label;
                directions[j] = start.equals(currentEdge.source);
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
