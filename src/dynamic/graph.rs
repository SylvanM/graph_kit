use std::{collections::{HashMap, HashSet, VecDeque}, hash::Hash};

use matrix_kit::dynamic::dmatrix::*;
use algebra_kit::algebra::PoRing;

// I'm sorry, but I'm making nodes implement Copy for my own sanity.
pub trait NodeType: Eq + Hash + Copy {}
impl NodeType for usize {}

/// A directed graph with node type `Node`, and edge weight type 
pub struct DiGraph<W: PoRing = i32, Node: NodeType = usize> {

    /// Because this graph is undirected, this adjacency matrix must be
    /// symmetric
    /// 
    /// adjacency_matrix[u, v] <-> edge (u, v)
    adjacency_matrix: Matrix<W>,

    /// The number of nodes in this graph
    num_nodes: usize,

    /// The internal mapping from matrix indices to generic node values
    index_to_node_map: HashMap<usize, Node>,

    /// The internal mapping from generic nodes to matrix indices
    node_to_index_map: HashMap<Node, usize>

}

impl<W: PoRing, Node: NodeType> DiGraph<W, Node> {

    pub type Edge = (Node, Node);

    fn check_invariant(&self) { // For debugging purposes!
        // // this is an undirected graph, so this matrix better be symmetric!
        // debug_assert!( 
        //     (0..self.num_nodes).all(|r|
        //         (0..self.num_nodes).all(|c|
        //             self.adjacency_matrix.get(r, c) == self.adjacency_matrix.get(c, r)
        //         )
        //     )
        // );
        // It's actually a DIRECTED graph now! But i'm keeping this code for the future ^^

        debug_assert_eq!(self.num_nodes, self.adjacency_matrix.row_count());
        debug_assert_eq!(self.num_nodes, self.index_to_node_map.len());
        debug_assert_eq!(self.num_nodes, self.node_to_index_map.len());

        // make sure the index mapping is total on [0, n), and that 
        // it corrsponds with the node -> index mapping
        debug_assert!(
            (0..self.num_nodes).all(|i|
                match self.index_to_node_map.get(&i) {
                    Some(node) => match self.node_to_index_map.get(&node) {
                        Some(index) => *index == i,
                        None => false,
                    },
                    None => false,
                }
            )
        )
    }

    // MARK: Constructors

    /// Creates an empty graph, with no nodes nor edges
    pub fn new() -> DiGraph<W> {
        let g = DiGraph { 
            adjacency_matrix: Matrix::from_flatmap(0, 0, Vec::new()), 
            num_nodes: 0,
            index_to_node_map: HashMap::new(),
            node_to_index_map: HashMap::new(),
        };

        g.check_invariant();

        g
    }

    /// Creates a graph with `n` nodes and no edges, with no node data
    pub fn new_with_node(n: usize) -> DiGraph<W> {
        let mut nodemap = HashMap::new();
        let mut indexmap = HashMap::new();

        for v in 0..n {
            nodemap.insert(v, v);
            indexmap.insert(v, v);
        }

        let g = DiGraph { 
            adjacency_matrix: Matrix::new(n, n),
            num_nodes: n,
            node_to_index_map: nodemap,
            index_to_node_map: indexmap,
        };

        g.check_invariant();

        g
    }

    /// Creates a directed graph from an adjacency list.
    /// 
    /// This implicitly assumes that the only nodes in the graph are those 
    /// touched by a given edge
    pub fn from_edge_list(edges: Vec<Self::Edge>) -> DiGraph<W, Node> {
        let mut node_set = HashSet::new();

        for (u, v) in edges.clone() {
            node_set.insert(u);
            node_set.insert(v);
        }

        // set up the correspondence!
        let mut index_to_node_map = HashMap::new();
        let mut node_to_index_map = HashMap::new();

        let mut index = 0;
        for node in node_set {
            // assign this node an index, and celebrate!
            node_to_index_map.insert(node, index);
            index_to_node_map.insert(index, node);

            index += 1;
        }

        let num_nodes = index;

        let mut adjacency_matrix = Matrix::<W>::new(num_nodes, num_nodes);

        // now, we set up the adjacency matrix!
        for (u, v) in edges {
            adjacency_matrix.set(
                *node_to_index_map.get(&u).unwrap(),
                *node_to_index_map.get(&v).unwrap(), 
                W::one()
            );
        }
        
        let g = DiGraph {
            adjacency_matrix,
            num_nodes,
            index_to_node_map,
            node_to_index_map,
        };

        g
    }

    // MARK: Properties

    /// Returns the number of nodes of this graph
    pub fn num_nodes(&self) -> usize {
        self.num_nodes
    }

    /// Returns the neighbors of a node
    pub fn neighbors(&self, node: &Node) -> HashSet<&Node> {
        let u = *self.node_to_index_map.get(node).unwrap();

        let mut neighbors = HashSet::new();

        for v in 0..self.num_nodes() {
            if !self.adjacency_matrix.get(u, v).is_zero() {
                neighbors.insert(self.index_to_node_map.get(&v).unwrap());
            }
        }

        neighbors
    }

    // MARK: Paths

    /// a BFS search from s to t, returning the shortest path as a 
    /// list of edges. If no path exists, return `None`
    /// 
    /// This shortest path is only in the *number* of edges, not edge costs
    /// 
    /// current implementation is mad inefficient
    pub fn bfs_search(&self, s: &Node, t: &Node) -> Option<Vec<Self::Edge>> {

        if !self.node_to_index_map.contains_key(s) {
            return None;
        }

        // visited[v] = Some(u) if v has been visited by u,
        // otherwise visited[v] = None
        let mut visited = vec![None ; self.num_nodes()]; 
        let mut frontier = VecDeque::new();
        frontier.push_front(s);

        while !frontier.is_empty() {
            let u = frontier.pop_front().unwrap();

            if u == t {
                break; // we're done!
            }

            for v in self.neighbors(u) {
                let index = *self.node_to_index_map.get(v).unwrap();
                if visited[index] == None {
                    visited[index] = Some(u);
                    frontier.push_back(v);
                }
            }
        }

        let mut path = Vec::new();
        
        let mut p = t;
        path.push(p);

        while p != s {
            if let Some(v) = visited[*self.node_to_index_map.get(p).unwrap()] {
                p = v;
                path.push(v);
            } else {
                // No path exists!
                return None;
            }
        }

        // now, construct an actual set of edges from this path!
        let mut edge_path = Vec::new();
        let mut recent_node = path.pop().unwrap(); // should be s!
        
        while let Some(next) = path.pop() {
            edge_path.push((*recent_node, *next));
            recent_node = next;
        }

        Some(edge_path)
    }

}

#[cfg(test)]
mod graph_tests {
    use super::DiGraph;


    #[test]
    fn test_bfs() {
        let graph = DiGraph::<i8>::from_edge_list(vec![
            (0, 1), (0, 3), (0, 5),
            (1, 2),
            (3, 1), (3, 4),
            (4, 2),
            (5, 3), (5, 4)
        ]);

        println!("{:?}", graph.bfs_search(&0, &2));
    }

}