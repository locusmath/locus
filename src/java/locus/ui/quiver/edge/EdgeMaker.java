package locus.ui.quiver.edge;
import locus.ui.quiver.line.LineFactory;
import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.paint.Color;
import javafx.scene.shape.*;
import javafx.scene.text.Text;

public class EdgeMaker {

    public static Group getEdge(Point2D start, Point2D control1, Point2D midPoint, Point2D control2, Point2D end, String label) {
        var g = new Group();

        // create the relevant content
        var p = CubicCurveUtilities.quadraticCubicCurve(start, control1, midPoint);
        p.setFill(null);
        p.setStroke(Color.BLACK);
        p.setStrokeWidth(1);

        var q = CubicCurveUtilities.quadraticCubicCurve(midPoint, control2, end);
        q.setFill(null);
        q.setStroke(Color.BLACK);
        q.setStrokeWidth(1);

        var width = (new Text(0,0,label)).getLayoutBounds().getWidth();
        var edgeLabel = new Text(midPoint.getX()-width/2, midPoint.getY()-4, label);

        var ori = CubicCurveEvaluator.eval(q, 1);
        var tan = CubicCurveEvaluator.evalDt(q, 1).normalize().multiply(6);
        var arrowHead = ArrowHeadMaker.makeArrowHead(
                new Point2D(ori.getX() - tan.getX() - tan.getY(), ori.getY() - tan.getY() + tan.getX()),
                ori,
                new Point2D(ori.getX() - tan.getX() + tan.getY(), ori.getY() - tan.getY() - tan.getX())
        );

        // finalize the process
        g.getChildren().addAll(p,q, arrowHead, edgeLabel);

        g.setOnMouseEntered((e) -> {
            p.setStroke(Color.RED);
            q.setStroke(Color.RED);
            arrowHead.setFill(Color.RED);
            arrowHead.setStroke(Color.RED);
            edgeLabel.setFill(Color.RED);
        });
        g.setOnMouseExited((e) -> {
            p.setStroke(Color.BLACK);
            q.setStroke(Color.BLACK);
            arrowHead.setFill(Color.BLACK);
            arrowHead.setStroke(Color.BLACK);
            edgeLabel.setFill(Color.BLACK);
        });

        return g;
    }

    public static Point2D getMidpoint(Point2D start, Point2D end, double factor) {
        var len = start.distance(end);
        var myLine = new Line(start.getX(), start.getY(), end.getX(), end.getY());
        var ourParametricLine = LineFactory.getParametricLine(myLine);
        return ourParametricLine.get(len * factor);
    }

    public static Group makeEdge(Point2D start, Point2D end, double factor, String label) {
        // get the midpoint
        var len = start.distance(end);
        var myLine = new Line(start.getX(), start.getY(), end.getX(), end.getY());
        var ourParametricLine = LineFactory.getParametricLine(myLine);
        var midPoint = ourParametricLine.get(len * factor);

        // get the control points
        var parallelLine = LineFactory.getParametricLine(myLine, midPoint);

        // the first control point
        var control1 = parallelLine.get(-len/2);

        // the second control point
        var control2 = parallelLine.get(len/2);

        var isFirstControlCloserToStart = control1.distance(start) >= control1.distance(end);

        if(isFirstControlCloserToStart) {
            return getEdge(start,control2,midPoint, control1, end, label);
        }

        return getEdge(start, control1, midPoint, control2, end, label);
    }

}
