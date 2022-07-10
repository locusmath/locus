package locus.graph.base;
import java.util.*;

/**
 * An abstract unlabeled directed graph. This defines the most common operations for dealing with
 * directed graphs entirely in terms of the IDigraph interface.
 */
public abstract class ADigraph implements IDigraph {

    public boolean isVertexLabeled() {
        return false;
    }

    public boolean isEdgeLabeled() {
        return false;
    }

    public boolean isDirected() {
        return true;
    }

    public boolean isUndirected() {
        return false;
    }

    /**
     * This computes the out degree of a vertex in a directed graph, where the out degree
     * is the number of vertices that are out neighbours of that element of the graph.
     *
     * @param n the argument vertex
     * @return the number of out neighbours of the vertex
     */
    public int outDegree(int n) {
        return outNeighbours(n).size();
    }

    /**
     * This computes the in degree of a vertex in a directed graph, where the in degree
     * is the number of vertices that are in neighbours of that element of the graph.
     *
     * @param n the argument vertex
     * @return the number of in neighbours of the vertex
     */
    public int inDegree(int n) {
        return inNeighbours(n).size();
    }

    /**
     * This computes the out degrees of all vertices in the directed graph and it returns them
     * in an integer array. The individual out degrees can be computed by the out degree function.
     *
     * @return the out degrees of all vertices in the directed graph
     */
    public int[] outDegrees() {
        var vertexCount = order();
        var rval = new int[vertexCount];

        for(int i = 0; i < vertexCount; i++) {
            rval[i] = outDegree(i);
        }

        return rval;
    }

    /**
     * This computes the in degrees of all vertices in the directed graph and it returns them
     * in an integer array. The individual in degrees can be computed by the in degree function.
     *
     * @return the in degrees of all vertices in the directed graph
     */
    public int[] inDegrees() {
        var vertexCount = order();
        var rval = new int[vertexCount];

        for(int i = 0; i < vertexCount; i++) {
            rval[i] = inDegree(i);
        }

        return rval;
    }

    /**
     * This tests if the vertex has any out neighbours or not.
     *
     * @param n the argument vertex
     * @return a boolean describing the existence of out neighbours
     */
    public boolean isSink(int n) {
        return outDegree(n) == 0;
    }

    /**
     * This tests if the vertex has any in neighbours or not.
     *
     * @param n the argument vertex
     * @return a boolean describing the existence of in neighbours
     */
    public boolean isSource(int n) {
        return inDegree(n) == 0;
    }

    /**
     * This computes all the sink vertices of the directed graph.
     *
     * @return all sink vertices of the digraph
     */
    public List<Integer> sinks() {
        var vertexCount = order();
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < vertexCount; i++) {
            if(isSink(i)) {
                rval.add(i);
            }
        }

        return rval;
    }

    /**
     * This computes all the source vertices of the directed graph.
     *
     * @return all source vertices of the digraph
     */
    public List<Integer> sources() {
        var vertexCount = order();
        var rval = new ArrayList<Integer>();

        for(int i = 0; i < vertexCount; i++) {
            if(isSource(i)) {
                rval.add(i);
            }
        }

        return rval;
    }

    /**
     * A digraph is reflexive provided that every vertex is a loop vertex.
     *
     * @return a boolean indicating reflexivity
     */
    public boolean isReflexive() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            rval &= (containsEdge(i,i));
        }

        return rval;
    }

    /**
     * A digraph is irreflexive provided that no vertex is a loop vertex.
     *
     * @return a boolean indicating irreflexivity
     */
    public boolean isIrreflexive() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            rval &= !(containsEdge(i,i));
        }

        return rval;
    }

    /**
     * A digraph is symmetric provided that for each edge (x,y) there exists
     * a corresponding edge (y,x) in the directed graph. Such a digraph can naturally
     * be considered to be equivalent to undirected graph.
     *
     * @return a boolean indicating symmetry
     */
    public boolean isSymmetric() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            for(int j = 0; j < i; j++) {
                var testCondition = ((containsEdge(i,j)) == (containsEdge(j,i)));
                rval &= testCondition;
            }
        }

        return rval;
    }

    /**
     * A digraph is antisymmetric provided that for each edge (x,y) it is never the case
     * that there exists a corresponding edge (y,x).
     *
     * @return a boolean indicating antisymmetry
     */
    public boolean isAntisymmetric() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            for(int j = 0; j < i; j++) {
                var testCondition = !(containsEdge(i,j) && containsEdge(j,i));
                rval &= testCondition;
            }
        }

        return rval;
    }

    /**
     * A directed garph is asymmetric provided that it is both antisymmetric and irreflexive.
     *
     * @return a boolean indicating asymmetry
     */
    public boolean isAsymmetric() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            rval &= !(containsEdge(i,i));

            for(int j = 0; j < i; j++) {
                var testCondition = !(containsEdge(i,j) && containsEdge(j,i));
                rval &= testCondition;
            }
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
     * This returns a list of all the loop vertices of a directed graph, where that list
     * can be determined by computing all the individual vertices of the directed graph
     * and checking rather or not they are a loop using isLoopVertex.
     *
     * @return all loop vertices of the digraph
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
     * This checks if the given directed graph is complete or not.
     *
     * @return a boolean indicating the completeness of this graph
     */
    public boolean isCompleteDigraph() {
        var vertexCount = order();
        var rval = true;

        for(int i= 0; i < vertexCount; i++) {
            for(int j = 0; j < vertexCount; j++) {
                rval &= containsEdge(i,j);
            }
        }

        return rval;
    }

    /**
     * A digraph is left total provided that for each vertex V there exists some
     * other vertex W such that (V,W) is an edge of the graph.
     *
     * @return a boolean indicating the left totalness of this graph
     */
    public boolean isLeftTotal() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            rval &= !isSink(i);
        }

        return rval;
    }

    /**
     * A digraph is right total provided that for each vertex V there exists some
     * other vertex W such that (W,V) is a vertex of the graph.
     *
     * @return a boolean indicating the right totalness of this graph
     */
    public boolean isRightTotal() {
        var vertexCount = order();
        var rval = true;

        for(int i = 0; i < vertexCount; i++) {
            rval &= !isSource(i);
        }

        return rval;
    }

    public Set<List<Integer>> outgoingEdgeLocations(int n) {
        var rval = new HashSet<List<Integer>>();
        var out = outNeighbours(n);

        for(Integer i : out) {
            rval.add(List.of(n,i));
        }

        return rval;
    }

    public Set<List<Integer>> incomingEdgeLocations(int n) {
        var rval = new HashSet<List<Integer>>();
        var out = inNeighbours(n);

        for(Integer i : out) {
            rval.add(List.of(i, n));
        }

        return rval;
    }

}
