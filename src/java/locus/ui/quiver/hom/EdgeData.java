package locus.ui.quiver.hom;

public class EdgeData {
    public Object obj;
    public String label;
    public Object source;
    public Object target;

    public EdgeData(Object obj, String label, Object source, Object target) {
        this.obj = obj;
        this.label = label;
        this.source = source;
        this.target = target;
    }

    public boolean isSimilarTo(EdgeData otherEdge) {
        return (source.equals(otherEdge.source) && target.equals(otherEdge.target)) ||
                (source.equals(otherEdge.target) && target.equals(otherEdge.source));
    }

    public String toString() {
        return label;
    }

}
