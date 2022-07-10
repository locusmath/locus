package locus.graph.base;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class DenseGraph extends AGraph {
    int order;
    boolean[][] edges;

    public DenseGraph(int order, boolean[][] edges) {
        this.order = order;
        this.edges = edges;
    }

    public DenseGraph(boolean[][] edges) {
        this.edges = edges;
        this.order = edges.length;
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

    @Override
    public Set<Set<Integer>> edgeLocations() {
        var rval = new HashSet<Set<Integer>>();

        for(int i = 0; i < order; i++) {
            for(int j = 0; j <= i; j++) {
                if(containsEdge(i,j)) {
                    var currentHashSet = new HashSet<Integer>();
                    currentHashSet.add(i);
                    currentHashSet.add(j);
                    rval.add(currentHashSet);
                }
            }
        }

        return rval;
    }

    public DenseGraph complement() {
        var newMatrix = new boolean[order][order];

        for(int i = 0; i < order; i++) {
            for(int j = 0; j < order; j++) {
                newMatrix[i][j] = !edges[i][j];
            }
        }

        return new DenseGraph(order, newMatrix);
    }

    public DenseGraph irreflexiveComplement() {
        var newMatrix = new boolean[order][order];

        for(int i = 0; i < order; i++) {
            for(int j = 0; j < order; j++) {
                newMatrix[i][j] = !(i == j) && !edges[i][j];
            }
        }

        return new DenseGraph(order, newMatrix);
    }

}
