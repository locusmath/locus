package locus.ui.util;
import javafx.event.EventHandler;
import javafx.scene.input.MouseEvent;
import javafx.scene.layout.Pane;

public class PannablePane extends Pane {
    private double pressedX, pressedY;

    public PannablePane() {
        setOnMousePressed(new EventHandler<MouseEvent>() {
            public void handle(MouseEvent event) {
                pressedX = event.getX();
                pressedY = event.getY();
            }
        });

        setOnMouseDragged(new EventHandler<MouseEvent>() {
            public void handle(MouseEvent event) {
                setTranslateX(getTranslateX() + event.getX() - pressedX);
                setTranslateY(getTranslateY() + event.getY() - pressedY);

                event.consume();
            }
        });
    }
}
