package locus.ui.quiver.line;

import javafx.geometry.Point2D;

import java.util.Optional;

public class VerticalLine extends ALine {
    public double x;

    public VerticalLine(double x) {
        this.x = x;
    }

    @Override
    public boolean isVertical() {
        return true;
    }

    @Override
    public boolean isHorizontal() {
        return false;
    }

    @Override
    public ILine parallelLine(Point2D point) {
        return new VerticalLine(point.getX());
    }

    public String toString() {
        return "x = " + Double.toString(x);
    }

    public boolean hasMultipleY(double x) {
        return this.x == x;
    }

    public boolean hasMultipleX(double y) {
        return false;
    }

    @Override
    public Optional<Double> getY(double x) {
        return Optional.empty();
    }

    @Override
    public Optional<Double> getX(double y) {
        return Optional.of(x);
    }

}
