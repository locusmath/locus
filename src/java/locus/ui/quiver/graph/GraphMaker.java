package locus.ui.quiver.graph;

import javafx.geometry.Point2D;
import javafx.scene.Group;
import javafx.scene.Scene;
import javafx.scene.transform.Scale;
import locus.ui.util.PannablePane;
import locus.ui.quiver.edge.VertexConnector;
import locus.ui.quiver.hom.HomMaker;
import locus.ui.quiver.hom.LoopMaker;
import locus.ui.quiver.vertex.VertexData;

import java.util.Hashtable;

public class GraphMaker {
    public static Group makeQuiver(Hashtable<Object, VertexData> nodes, Object[][] homClasses, GraphActionListener listener) {
        var rval = new Group();

        for(var i : nodes.entrySet()) {
            var vertexNode = i.getValue().toVertexNode();
            var currentKey = i.getKey();

            vertexNode.setOnMouseClicked((e) -> {
                listener.vertexAction(currentKey);
            });

            rval.getChildren().add(vertexNode);
        }

        for(var i : homClasses) {
            var source = i[0];
            var target = i[1];
            var labels = (String[]) i[2];

            var sourceData = nodes.get(source);
            var targetData = nodes.get(target);

            var rect1 = sourceData.bounds;
            var rect2 = targetData.bounds;

            var connector = VertexConnector.rectangleConnector(rect1, rect2);
            var start = new Point2D(connector.getStartX(), connector.getStartY());
            var end = new Point2D(connector.getEndX(), connector.getEndY());

            boolean[] directions = (boolean[]) i[3];
            Object[] ids = (Object[]) i[4];

            var table = new Hashtable<Object, Group>();
            var currentHom = (!source.equals(target)) ?
                    HomMaker.makeHomClass(start, end, rect1, rect2, ids, labels, directions, table) :
                    LoopMaker.makeLoopClass(rect1, ids, labels, table);

            for(var entry : table.entrySet()) {
                var key = entry.getKey();
                entry.getValue().setOnMouseClicked((e) -> {
                    listener.edgeAction(key);
                });
            }

            rval.getChildren().add(currentHom);
        }

        return rval;
    }

    public static Scene makeGraphScene(Hashtable<Object, VertexData> nodes, Object[][] homClasses, GraphActionListener listener, int width, int height) {
        var pane = new PannablePane();
        var q = GraphMaker.makeQuiver(nodes, homClasses, listener);
        pane.getChildren().add(q);

        Scene scene = new Scene(pane, width, height);
        scene.setOnKeyPressed((e) -> {
            if(e.isControlDown() && e.getText().equals("+") || e.getText().equals("=")) {
                var newScale = new Scale();
                newScale.setX( pane.getScaleX() * 1.05);
                newScale.setY(pane.getScaleY() * 1.05);
                pane.getTransforms().add(newScale);
            } else if(e.isControlDown() && e.getText().equals("-")) {
                var newScale = new Scale();
                newScale.setX( pane.getScaleX() * 1/1.05);
                newScale.setY(pane.getScaleY() * 1/1.05);
                pane.getTransforms().add(newScale);
            }
        });

        return scene;
    }

}
