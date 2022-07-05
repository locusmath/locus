 package locus.graph;
 import java.util.List;
 import java.util.Set;

 /**
  * The core abstraction of undirected unlabeled graphs. A labeled undirected
  * graph can be defined over an undirected graph of this form using some
  * labeling scheme.
  */
 interface IGraph {

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
      * This method checks if an edge exists at a given location.
      *
      * @param x the first coordinate of the edge
      * @param y the second coordinate of the edge
      * @return a boolean indicating existence of the given edge
      */
    public boolean containsEdge(int x, int y);

     /**
      * This method gets the undirected neighbours of a vertex.
      *
      * @param n the argument vertex
      * @return the neighbours of the vertex
      */
    public List<Integer> neighbours(int n);

     /**
      * Get the edges of the graph as a set system.
      *
      * @return the location of edges in the graph
      */
    public Set<Set<Integer>> edgeLocations();

}