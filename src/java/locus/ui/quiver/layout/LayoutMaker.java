package locus.ui.quiver.layout;
import javafx.scene.shape.Rectangle;
import javafx.scene.text.Text;
import locus.ui.quiver.vertex.VertexData;

import java.util.Hashtable;

public class LayoutMaker {

    public static Hashtable<Object, VertexData> layoutGraph(LabeledEntity[][] coll) {
        var collLength = coll.length;
        if(collLength == 0) {
            return new Hashtable<Object, VertexData>();
        }

        Text[][] texts = new Text[collLength][coll[0].length];

        // layout information
        double overallHeight = 0;
        double[] widths = new double[collLength];
        double[] heights = new double[collLength];

        // gaps between nodes
        double hgap = 100;
        double vgap = 100;

        for(int i = 0; i < collLength; i++) {
            var column = coll[i];
            var columnHeight = 0;
            var maxWidth = 0;

            for(int j = 0; j < column.length; j++) {
                var currentString = column[j].label;
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
        for(int i = 0; i < collLength; i++) {
            var column = coll[i];

            var currentY = startY + (overallHeight-heights[i])/2;
            for(int j = 0; j < column.length; j++) {
                var currentObject = column[j].obj;
                var currentString = column[j].label;
                var currentText = texts[i][j];
                var currentWidth = currentText.getLayoutBounds().getWidth()+100;
                var currentHeight = currentText.getLayoutBounds().getHeight()+100;

                rval.put(currentObject, new VertexData(currentString, new Rectangle(currentX, currentY, currentWidth, currentHeight)));

                currentY += currentText.getLayoutBounds().getHeight()+vgap;
            }
            currentX += widths[i]+hgap;
        }

        return rval;
    }
}
