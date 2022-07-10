package locus.graph.base;

import java.util.*;

public class DenseDigraph extends ADigraph {
    int order;
    boolean[][] edges;

    public DenseDigraph(boolean[][] edges) {
        this.edges = edges;
        this.order = edges.length;
    }

    public DenseDigraph(int order, boolean[][] edges) {
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

        for(int y = 0; y < order; y++) {
            for(int x = 0; x < order; x++) {
                if(containsEdge(x,y)) {
                    rval++;
                }
            }
        }

        return rval;
    }

    @Override
    public boolean containsEdge(int x, int y) {
        return this.edges[x][y];
    }

    @Override
    public List<Integer> outNeighbours(int n) {
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < order; i++) {
            var testCondition = edges[n][i];
            if(testCondition) {
                rval.add(i);
            }
        }

        return rval;
    }

    @Override
    public List<Integer> inNeighbours(int n) {
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < order; i++) {
            var testCondition = edges[i][n];
            if(testCondition) {
                rval.add(i);
            }
        }

        return rval;
    }

    public Set<List<Integer>> edgeLocations() {
        var rval = new HashSet<List<Integer>>();

        for(int x = 0; x < order; x++) {
            for(int y = 0; y < order; y++) {
                if(edges[x][y]) {
                    rval.add(Arrays.asList((Integer) x, (Integer) y));
                }
            }
        }

        return rval;
    }

    public DenseDigraph complement() {
        var newMatrix = new boolean[order][order];

        for(int i = 0; i < order; i++) {
            for(int j = 0; j < order; j++) {
                newMatrix[i][j] = !edges[i][j];
            }
        }

        return new DenseDigraph(order, newMatrix);
    }

    public DenseDigraph transpose() {
        var newMatrix = new boolean[order][order];

        for(int i = 0; i < order; i++) {
            for(int j = 0; j < order; j++) {
                newMatrix[i][j] = edges[j][i];
            }
        }

        return new DenseDigraph(order, newMatrix);
    }

    public DenseDigraph symmetricClosure() {
        var newMatrix = new boolean[order][order];

        for(int i = 0; i < order; i++) {
            for(int j = 0; j <= i; j++) {
                var testCondition = edges[i][j] || edges[j][i];
                if(testCondition) {
                    newMatrix[i][j] = true;
                    newMatrix[j][i] = true;
                }
            }
        }

        return new DenseDigraph(order, newMatrix);
    }

    public DenseGraph toUndirected() {
        var symmetricClosureDigraph = symmetricClosure();
        return new DenseGraph(order, symmetricClosureDigraph.edges);
    }

}
