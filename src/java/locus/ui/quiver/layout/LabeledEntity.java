package locus.ui.quiver.layout;

public class LabeledEntity {
    String label;
    Object obj;
    public LabeledEntity(String label, Object obj) {
        this.label = label;
        this.obj = obj;
    }

    public LabeledEntity(String label) {
        this.label = label;
        this.obj = label;
    }

    public String toString() {
        return label;
    }

    public static LabeledEntity getInstance(Object obj) {
        return new LabeledEntity(obj.toString(), obj);
    }

}
