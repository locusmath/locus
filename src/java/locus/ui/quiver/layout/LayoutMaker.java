package locus.ui.quiver.layout;

import javafx.scene.shape.Rectangle;
import javafx.scene.text.Text;
import locus.ui.quiver.vertex.VertexData;

import java.util.Hashtable;

public class LayoutMaker {

    public static Hashtable<Object, VertexData> layoutGraph(String[][] coll) {
        if(coll.length == 0) {
            return new Hashtable<Object, VertexData>();
        }

        Text[][] texts = new Text[coll.length][coll[0].length];

        // layout information
        double overallHeight = 0;
        double[] widths = new double[coll.length];
        double[] heights = new double[coll.length];

        // gaps between nodes
        double hgap = 50;
        double vgap = 100;

        for(int i = 0; i < coll.length; i++) {
            var column = coll[i];
            var columnHeight = 0;
            var maxWidth = 0;

            for(int j = 0; j < column.length; j++) {
                var currentString = column[j];
                var currentText = new Text(currentString);
                texts[i][j] = currentText;

                var currentWidth = currentText.getLayoutBounds().getWidth()+10;
                var currentHeight = currentText.getLayoutBounds().getHeight()+10;

                columnHeight += currentHeight+ hgap;
                maxWidth = Math.max(maxWidth, (int) currentWidth);
            }

            widths[i] = maxWidth;
            heights[i] = columnHeight;
            overallHeight = Math.max(overallHeight, columnHeight);
        }

        var startX = 100;
        var startY = 100;

        var rval = new Hashtable<Object, VertexData>();
        var currentX = startX;
        for(int i = 0; i < coll.length; i++) {
            var column = coll[i];

            var currentY = startY + (overallHeight-heights[i])/2;
            for(int j = 0; j < column.length; j++) {
                var currentString = coll[i][j];
                var currentText = texts[i][j];
                var currentWidth = currentText.getLayoutBounds().getWidth()+10;
                var currentHeight = currentText.getLayoutBounds().getHeight()+10;

                rval.put(currentString, new VertexData(currentString, new Rectangle(currentX, currentY, currentWidth, currentHeight)));

                currentY += currentText.getLayoutBounds().getHeight()+vgap;
            }
            currentX += widths[i]+hgap;
        }

        return rval;
    }
}
