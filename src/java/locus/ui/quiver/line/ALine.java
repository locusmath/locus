package locus.ui.quiver.line;
import javafx.geometry.Point2D;
import javafx.scene.shape.Rectangle;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;

public abstract class ALine implements ILine {

    public Optional<Point2D> getPointByX(double x) {
        var oy = getY(x);

        if(oy.isPresent()) {
            return Optional.of(new Point2D(x, oy.get()));
        } else {
            return Optional.empty();
        }

    }

    public Optional<Point2D> getPointByY(double y) {
        var ox = getX(y);

        if(ox.isPresent()) {
            return Optional.of(new Point2D(ox.get(), y));
        } else {
            return Optional.empty();
        }

    }

    public HashSet<Point2D> getVerticalIntersections(double x, double minY, double maxY) {
        if(hasMultipleY(x)) {
            return new HashSet<Point2D>(List.of(new Point2D(x,minY), new Point2D(x,maxY)));
        } else {
            var optionalY = getY(x);
            if(optionalY.isPresent()) {
                double myY = optionalY.get();
                if(minY <= myY && myY <= maxY) {
                    var p = new Point2D(x,myY);
                    return new HashSet<Point2D>(List.of(p));
                }
            }
        }

        return new HashSet<Point2D>();
    }

    public HashSet<Point2D> getHorizontalIntersections(double y, double minX, double maxX) {
        if(hasMultipleX(y)) {
            return new HashSet<Point2D>((List.of(new Point2D(minX, y), new Point2D(maxX, y))));
        } else {
            var optionalX = getX(y);
            if(optionalX.isPresent()) {
                double myX = optionalX.get();
                if(minX <= myX && myX <= maxX) {
                    var p = new Point2D(myX, y);
                    return new HashSet<Point2D>(List.of(p));
                }
            }
        }

        return new HashSet<Point2D>();
    }

    public HashSet<Point2D> getRectangleIntersections(double x, double y, double width, double height) {
        var v1 = getVerticalIntersections(x, y, y+height);
        var v2 = getVerticalIntersections(x+width,y,y+height);
        var h1 = getHorizontalIntersections(y, x, x+width);
        var h2 = getHorizontalIntersections(y+height,x,x+width);

        var rval = new HashSet<Point2D>(v1);
        rval.addAll(v2);
        rval.addAll(h1);
        rval.addAll(h2);
        return rval;
    }

    public Point2D getNearestIntersection(double x, double y, double width, double height, Point2D point) {
        return LineFactory.getNearestPoint(
                getRectangleIntersections(x,y,width,height),
                point
        );
    }

    public Point2D getNearestIntersection(Rectangle rect, Point2D point) {
        return getNearestIntersection(rect.getX(), rect.getY(), rect.getWidth(), rect.getHeight(), point);
    }

}
