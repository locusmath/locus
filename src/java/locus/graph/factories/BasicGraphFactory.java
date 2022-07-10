package locus.graph.factories;
import locus.graph.base.DenseGraph;
import locus.graph.base.SparseGraph;
import java.util.Arrays;
import java.util.List;
import java.util.stream.IntStream;

public class BasicGraphFactory {

    public static SparseGraph emptyGraph(int n) {
        var adjacency = new List[n];
        for(int i = 0; i < n; i++) {
            adjacency[i] = List.of();
        }
        return new SparseGraph(n, adjacency);
    }

    public static DenseGraph completeGraph(int n) {
        // full true boolean matrix
        boolean[] rowArray = new boolean[n];
        Arrays.fill(rowArray, true);
        boolean[][] matrix = new boolean[n][n];
        Arrays.fill(matrix, rowArray);

        return new DenseGraph(n, matrix);
    }

    public static DenseGraph completeSimpleGraph(int n) {
        var rval = new boolean[n][n];

        for(int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                rval[i][j] = !(i == j);
            }
        }

        return new DenseGraph(n, rval);
    }

    public static SparseGraph starGraph(int n) {
        var adjacency = new List[n];
        adjacency[0] = IntStream.range(1,n).boxed().toList();

        for(int i = 1; i < n; i++) {
            adjacency[i] = List.of(0);
        }

        return new SparseGraph(n, adjacency);
    }

    public static SparseGraph cycleGraph(int n) {
        if(n <= 1) {
            return emptyGraph(n);
        }

        var adjacency = new List[n];

        for(int i = 0; i < n; i++) {
            var next = (i+1) % n;
            var previous = (n+(i-1)) % n;

            adjacency[i] = List.of(next, previous);
        }

        return new SparseGraph(n, adjacency);
    }

    public static SparseGraph pathGraph(int n) {
        if(n <= 1) {
            return emptyGraph(n);
        }

        var adjacency = new List[n];

        for(int i = 0; i < n; i++) {
            var next = (i+1) % n;
            var previous = (n+(i-1)) % n;

            if(i == 0) {
                adjacency[i] = List.of(next);
            } else if(i == (n-1)) {
                adjacency[i] = List.of(previous);
            } else {
                adjacency[i] = List.of(next,previous);
            }
        }

        return new SparseGraph(n, adjacency);
    }


}
