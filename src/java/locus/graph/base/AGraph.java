package locus.graph.base;
import java.util.ArrayList;
import java.util.List;

/**
 * An abstract undirected graph class. This defines all the methods needed for dealing with
 * undirected graphs entirely in terms of the IGraph interface.
 */
public abstract class AGraph implements IGraph {

    public boolean isVertexLabeled() {
        return false;
    }

    public boolean isEdgeLabeled() {
        return false;
    }

    public boolean isDirected() {
        return false;
    }

    public boolean isUndirected() {
        return true;
    }

    /**
     * The degree of a vertex in an undirected graph is the number of vertices that are
     * adjacent to that vertex in the graph.
     *
     * @param n the agrument vertex
     * @return the degree of the vertex
     */
    public int degree(int n) {
        return neighbours(n).size();
    }

    /**
     * This returns an integer array of all the different degrees of vertices in the graph,
     * where the individual degrees can be computed by the degree function.
     *
     * @return the degrees of the graph
     */
    public int[] degrees() {
        var vertexCount = order();
        var rval = new int[vertexCount];

        for(int i = 0; i < vertexCount; i++) {
            rval[i] = degree(i);
        }

        return rval;
    }

    /**
     * This returns true provided that the argument vertex at the given index location
     * is a loop vertex, meaning that there is an edge (n,n) in the graph.
     *
     * @param n an argument vertex
     * @return a boolean indicating rather or not n is a loop
     */
    public boolean isLoopVertex(int n) {
        return containsEdge(n,n);
    }

    /**
     * This returns the subset of vertices of the graph that are loops, where a loop is a vertex
     * that is adjacent to itself.
     *
     * @return the loop vertices of the graph
     */
    public List<Integer> loopVertices() {
        var vertexCount = order();
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < vertexCount; i++) {
            if(containsEdge(i,i)) {
                rval.add(i);
            }
        }

        return rval;
    }

    /**
     * This returns the number of loops in the graph.
     *
     * @return the number of loops in the graph
     */
    public int numberOfLoops() {
        var vertexCount = order();
        var rval = 0;

        for(int i = 0; i < vertexCount; i++) {
            if(isLoopVertex(i)) {
                rval++;
            }
        }

        return rval;
    }

    /**
     * This checks if the given undirected graph is complete or not.
     *
     * @return a boolean indicating the completeness of this graph
     */
    public boolean isCompleteGraph() {
        var vertexCount = order();
        var rval = true;

        for(int i= 0; i < vertexCount; i++) {
            for(int j = 0; j < vertexCount; j++) {
                rval &= containsEdge(i,j);
            }
        }

        return rval;
    }

}
