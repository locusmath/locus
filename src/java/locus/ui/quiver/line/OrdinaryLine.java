package locus.ui.quiver.line;

import javafx.geometry.Point2D;

import java.util.Optional;

public class OrdinaryLine extends ALine {
    public double m;
    public double b;

    public OrdinaryLine(double slope, double yIntercept) {
        this.m = slope;
        this.b = yIntercept;
    }

    @Override
    public boolean isVertical() {
        return false;
    }

    @Override
    public boolean isHorizontal() {
        return (m==0);
    }

    @Override
    public ILine parallelLine(Point2D point) {
        var x = point.getX();
        var y = point.getY();

        var b = y - m*x;
        return new OrdinaryLine(m, b);
    }

    public String toString() {
        return "y = " + Double.toString(this.m) + "x + " + Double.toString(this.b);
    }

    public boolean hasMultipleY(double x) {
        return false;
    }

    public boolean hasMultipleX(double y) {
        return (m==0) && (b==y);
    }

    @Override
    public Optional<Double> getY(double x) {
        return Optional.of(m*x + b);
    }

    @Override
    public Optional<Double> getX(double y) {
        if(m == 0) {
            return Optional.empty();
        }

        return Optional.of((y - this.b) / this.m);
    }

    public Point2D directionVector() {
        // select the start and end points
        var a1 = this.getPointByX(1);
        var a2 = this.getPointByX(0);

        // get the optional values
        Point2D p1 = a1.get();
        Point2D p2 = a2.get();

        // compute the direction vector
        Point2D differenceVector = new Point2D(p1.getX() - p2.getX(), p1.getY() - p2.getY());
        var x = differenceVector.getX();
        var y = differenceVector.getY();
        var l = Math.sqrt(x*x +y*y);
        return new Point2D(x/l, y/l);
    }

}
