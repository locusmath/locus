package locus.ui.util;
import javafx.application.Platform;
import javafx.collections.FXCollections;
import javafx.collections.ObservableList;
import javafx.embed.swing.JFXPanel;
import javafx.scene.Group;
import javafx.scene.Scene;
import javafx.scene.chart.PieChart;
import javafx.scene.paint.Color;
import javafx.scene.text.Font;
import javafx.scene.text.Text;
import javax.swing.JFrame;
import javax.swing.SwingUtilities;

public class SceneViewer extends JFrame {

    public SceneViewer(String title, Scene scene) {
        SwingUtilities.invokeLater(new Runnable() {
            @Override
            public void run() {
                var frame = new JFrame(title);
                final JFXPanel fxPanel = new JFXPanel();
                frame.getContentPane().add(fxPanel);
                frame.setSize(600, 600);
                frame.setVisible(true);
                Platform.runLater(new Runnable() {
                    @Override
                    public void run() {
                        fxPanel.setScene(scene);
                    }
                });
            }
        });
    }

}
