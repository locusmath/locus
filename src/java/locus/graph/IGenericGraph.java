package locus.graph;

/**
 * Methods for graphs that are common to both directed
 * and undirected graph types.
 */
public interface IGenericGraph {

    /**
     * The number of vertices of a graph.
     *
     * @return the number of vertices of this graph.
     */
    public int order();

    /**
     * The number of edges of a graph.
     *
     * @return the number of edges in this graph.
     */
    public int size();

    /**
     * This checks if the vertices of this graph are labeled.
     *
     * @return rather or not this graph is vertex labeled
     */
    public boolean isVertexLabeled();

    /**
     * This checks if the edges of this graph are labeled.
     *
     * @return rather or not this graph is edge labeled
     */
    public boolean isEdgeLabeled();

}
