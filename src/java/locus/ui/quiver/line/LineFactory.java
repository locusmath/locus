package locus.ui.quiver.line;
import javafx.geometry.Point2D;
import javafx.scene.shape.Line;

import java.util.HashSet;

public class LineFactory {

    public static Point2D getNearestPoint(HashSet<Point2D> coll, Point2D point) {
        var len = coll.size();
        if(len == 0) {
            return null;
        }

        var iterator = coll.iterator();
        var currentPoint = iterator.next();
        while(iterator.hasNext()) {
            var nextPoint = iterator.next();
            var currentDistance = currentPoint.distance(point);
            var nextDistance = nextPoint.distance(point);

            if(nextDistance < currentDistance) {
                currentPoint = nextPoint;
            }
        }

        return currentPoint;
    }

    public static double slope(double x1, double y1, double x2, double y2) {
        return (y2-y1) / (x2-x1);
    }

    public static double yIntercept(double x1, double y1, double x2, double y2) {
        var m = slope(x1,y1,x2,y2);
        return y1 - m*x1;
    }

    public static ALine makeLine(double x1, double y1, double x2, double y2) {
        if(x1 == x2) {
            return new VerticalLine(x1);
        } else {
            var m = slope(x1,y1,x2,y2);
            var b = yIntercept(x1,y1,x2,y2);
            return new OrdinaryLine(m, b);
        }
    }

    public static ALine makeLine(Point2D start, Point2D end) {
        return makeLine(start.getX(), start.getY(), end.getX(), end.getY());
    }

    public static ALine makeLine(Line line) {
        return makeLine(line.getStartX(), line.getStartY(), line.getEndX(), line.getEndY());
    }

    public static Point2D midpoint(Line line) {
        return new Point2D(
                line.getStartX() + (line.getEndX() - line.getStartX()) /2,
                line.getStartY() + (line.getEndY() - line.getStartY()) / 2);
    }

    public static ALine perpindicularLine(Line line, Point2D midpoint) {
        var parentLine = makeLine(line);

        if(parentLine.isVertical()) {
            return new OrdinaryLine(0, midpoint.getY());
        } else if(parentLine.isHorizontal()) {
            return new VerticalLine(midpoint.getX());
        } else {
            var ordinaryLine = (OrdinaryLine) parentLine;
            var perpindicularSlope = -(1/ordinaryLine.m);
            var b = midpoint.getY() - perpindicularSlope* midpoint.getX();
            return new OrdinaryLine(perpindicularSlope, b);
        }
    }

    public static ALine perpindicularLine(Line line) {
        return perpindicularLine(line, midpoint(line));
    }

    public static IParametricLine getParametricLine(ILine line, Point2D midpoint) {

        if(line.isVertical()) {
            var x = ((VerticalLine) line).x;

            return new IParametricLine() {
                @Override
                public Point2D get(double arg) {
                    return new Point2D(x, midpoint.getY() + arg);
                }
            };

        } else {
            var ordinaryLine = (OrdinaryLine) line;
            var direction = ordinaryLine.directionVector();

            return new IParametricLine() {
                @Override
                public Point2D get(double arg) {
                    return new Point2D(midpoint.getX() + arg* direction.getX(), midpoint.getY() + arg*direction.getY());
                }
            };
        }

    }

    public static IParametricLine getParametricLine(Line line, Point2D midpoint) {
        return getParametricLine(makeLine(line), midpoint);
    }

    public static IParametricLine getParametricLine(Line line) {
        return getParametricLine(perpindicularLine(line), midpoint(line));
    }

}
