package locus.graph;

import java.util.List;

public class SparseGraph extends AGraph {
    int order;
    List<Integer>[] edges;

    @Override
    public int order() {
        return order;
    }

    @Override
    public int size() {
        var rval = 0;
        for(int i = 0; i < order; i++) {
            for(int j = 0; j <= i; j++) {
                rval += containsEdge(i,j) ? 1 : 0;
            }
        }
        return rval;
    }

    @Override
    public boolean containsEdge(int x, int y) {
        return edges[x].contains(y);
    }

    @Override
    public List<Integer> neighbours(int n) {
        return edges[n];
    }

}
