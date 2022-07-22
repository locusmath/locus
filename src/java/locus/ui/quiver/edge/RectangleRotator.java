package locus.ui.quiver.edge;

import javafx.geometry.Point2D;
import javafx.scene.shape.Rectangle;

public class RectangleRotator {

    public static Point2D getHorizontalLineCoordinate(double y, double minX, double maxX, double factor, boolean forwards) {
        var distance = Math.abs(maxX-minX);
        var adjustedDistance = distance * factor;

        var myX = forwards ? minX + adjustedDistance : maxX - adjustedDistance;
        return new Point2D(myX, y);
    }

    public static Point2D getVerticalLineCoordinate(double x, double minY, double maxY, double factor, boolean forwards) {
        var distance = Math.abs(maxY-minY);
        var adjustedDistance = distance * factor;

        var myY = forwards ? minY + adjustedDistance : maxY - adjustedDistance;
        return new Point2D(x, myY);
    }

    public static double getHorizontalLineFactor(double x, double y, double minX, double maxX, boolean forwards) {
        var distance = Math.abs(maxX-minX);
        var currentDistance = forwards ? x-minX : maxX-x;
        return currentDistance/distance;
    }

    public static double getVerticalLineFactor(double x, double y, double minY, double maxY, boolean forwards) {
        var distance = Math.abs(maxY-minY);
        var currentDistance = forwards ? y-minY : maxY-y;
        return currentDistance/distance;
    }

    public static Point2D getRectangleCoordinate(Rectangle rect, double arg) {
        var factor = arg - Math.floor(arg);

        if(0.0 <= factor && factor <= 0.25) {
            var adjustedFactor = factor*4;
            return getHorizontalLineCoordinate(rect.getY(), rect.getX(), rect.getX()+rect.getWidth(), adjustedFactor, true);
        } else if(0.25 < factor && factor <= 0.5) {
            var adjustedFactor = (factor-0.25) * 4;
            return getVerticalLineCoordinate(rect.getX()+rect.getWidth(), rect.getY(), rect.getY()+rect.getHeight(), adjustedFactor, true);
        } else if(0.5 < factor && factor <= 0.75) {
            var adjustedFactor = (factor-0.5) * 4;
            return getHorizontalLineCoordinate(rect.getY()+rect.getHeight(), rect.getX(),rect.getX()+rect.getWidth(), adjustedFactor, false);
        } else {
            var adjustedFactor = (factor-0.75) * 4;
            return getVerticalLineCoordinate(rect.getX(), rect.getY(), rect.getY()+rect.getHeight(), adjustedFactor, false);
        }

    }

    public static double getRectangleFactor(Rectangle rect, Point2D point) {
        var y = point.getY();
        var x = point.getX();

        var minX = rect.getX();
        var maxX = rect.getX() + rect.getWidth();
        var minY = rect.getY();
        var maxY = rect.getY() + rect.getHeight();

        if(point.getY() == minY) {
            var num = getHorizontalLineFactor(x,y,minX,maxX, true);
            return num/4;
        }

        if(point.getX() == maxX) {
            var num = getVerticalLineFactor(x,y,minY,maxY, true);
            return 0.25 + num/4;
        }

        if(point.getY() == maxY) {
            var num = getHorizontalLineFactor(x,y,minX,maxX, false);
            return 0.5 + num/4;
        }

        if(point.getX() == minX) {
            var num = getVerticalLineFactor(x,y,minY,maxY, false);
            return 0.75 + num/4;
        }

        return 0;
    }

}
