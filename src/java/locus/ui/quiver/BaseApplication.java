package locus.ui.quiver;
import javafx.scene.Scene;
import javafx.scene.layout.Pane;
import javafx.application.Application;
import javafx.stage.Stage;
import java.io.IOException;

public class BaseApplication extends Application {
    @Override
    public void start(Stage stage) throws IOException {
        stage.setScene(new Scene(new Pane(), 600, 600));
        stage.show();
    }

    public static void main(String[] args) {
        launch();
    }

}