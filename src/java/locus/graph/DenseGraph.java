package locus.graph;
import java.util.ArrayList;
import java.util.List;

public class DenseGraph extends AGraph {
    int order;
    boolean[][] edges;

    public DenseGraph(int order, boolean[][] edges) {
        this.order = order;
        this.edges = edges;
    }

    @Override
    public int order() {
        return order;
    }

    @Override
    public int size() {
        var rval = 0;
        for(int i = 0; i < order; i++) {
            for(int j = 0; j <= i; j++) {
                rval += edges[i][j] ? 1 : 0;
            }
        }
        return rval;
    }

    @Override
    public boolean containsEdge(int x, int y) {
        return edges[x][y];
    }

    @Override
    public List<Integer> neighbours(int n) {
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < order; i++) {
            if(containsEdge(n,i)) {
                rval.add(i);
            }
        }

        return rval;
    }

}
