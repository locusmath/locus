package locus.graph;

import java.util.*;

public class SparseDigraph extends ADigraph {
    int order;
    List<Integer>[] edges;

    public SparseDigraph(int order, List<Integer>[] edges) {
        this.order = order;
        this.edges = edges;
    }

    public SparseDigraph(List<Integer>[] edges) {
        this.order = edges.length;
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
            rval += edges[i].size();
        }

        return rval;
    }

    @Override
    public boolean containsEdge(int x, int y) {
        return edges[x].contains(y);
    }

    @Override
    public List<Integer> outNeighbours(int n) {
        return edges[n];
    }

    @Override
    public List<Integer> inNeighbours(int n) {
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < order; i++) {
            if(containsEdge(i,n)) {
                rval.add(i);
            }
        }

        return rval;
    }

    @Override
    public Set<List<Integer>> edgeLocations() {
        var rval = new HashSet<List<Integer>>();

        for(int i = 0; i < order; i++) {
            for(var item : edges[i]) {
                rval.add(Arrays.asList(i,item));
            }
        }

        return rval;
    }

}
