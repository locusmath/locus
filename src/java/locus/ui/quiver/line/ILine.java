package locus.ui.quiver.line;
import javafx.geometry.Point2D;
import java.util.Optional;

public interface ILine {

    public boolean isVertical();
    public boolean isHorizontal();

    public ILine parallelLine(Point2D point);

    public boolean hasMultipleY(double x);

    public boolean hasMultipleX(double y);

    public Optional<Double> getY(double x);
    public Optional<Double> getX(double y);

}
