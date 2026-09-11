use core::fmt;
use std::{collections::{HashMap, HashSet}, debug_assert, debug_assert_eq, hash::Hash};

use matrix_kit::dynamic::matrix::*;
use algebra_kit::algebra::PoRing;

pub trait NodeType: Eq + Hash + Copy {}
impl NodeType for usize {}

/// A raw graph with node type `Node` and edge weight type `W`
/// 
/// We care about speed far more than memory, meaning we'll
/// store a bunch of copies of the graph in redundant ways.
pub struct Graph<Node: NodeType = usize, W: PoRing = i32> {

    /// Adjacency matrix!
    adjacency_matrix: Matrix<i8>,

    /// A weight matrix, assigning a weight to every edge
    weight_matrix: Matrix<W>,

    /// The number of nodes in this graph
    num_nodes: usize,

    /// Internal mapping from node indices to generic node values
    index_to_node_map: HashMap<usize, Node>,

    /// Internal mapping from generic nodes to node indices
    node_to_index_map: HashMap<Node, usize>,

    /// Map from a node to its directed neighbors
    directed_neighbors_map: HashMap<Node, Vec<Node>>,

    /// Map from a node to its undirected neighbors
    undirected_neighbors_map: HashMap<Node, Vec<Node>>,

    /// A set of all directed edges in this graph
    directed_edge_set: HashSet<(Node, Node)>,

    /// A set of all undirected edges in this graph
    undirected_edge_set: HashSet<(Node, Node)>,

}

impl<Node: NodeType, W: PoRing> Graph<Node, W> {

    fn node_to_index(&self, node: Node) -> usize {
        *self.node_to_index_map.get(&node).unwrap()
    }

    fn index_to_node(&self, index: usize) -> Node {
        *self.index_to_node_map.get(&index).unwrap()
    }

    fn check_invariant(&self) {
        // the adjacency matrix is ground truth.

        debug_assert_eq!(self.num_nodes, self.adjacency_matrix.row_count(), "Adjacency matrix wrong height");
        debug_assert_eq!(self.num_nodes, self.adjacency_matrix.col_count(), "Adjacency matrix wrong width");

        debug_assert_eq!(self.num_nodes, self.weight_matrix.row_count(), "Weight matrix wrong height");
        debug_assert_eq!(self.num_nodes, self.weight_matrix.col_count(), "Weight matrix wrong width");

        debug_assert_eq!(self.num_nodes, self.index_to_node_map.keys().count(), "Index -> Node map wrong size");
        debug_assert_eq!(self.num_nodes, self.node_to_index_map.keys().count(), "Node -> Index map wrong size");

        // Make sure the index mapping is total on [0, n), and that it 
        // corresponds with the node -> index mapping
        debug_assert!(
            (0..self.num_nodes).all(|i|
                match self.index_to_node_map.get(&i) {
                    Some(node) => match self.node_to_index_map.get(&node) {
                        Some(index) => *index == i,
                        None => false,
                    },
                    None => false,
                }
            ),
            "Index <-> Node maps are malformed"
        );

        // Make sure *_neighbors_map has no erroneous entries
        // This includes checking that u_neighbors returns a proper set
        for node in self.node_set() {
            let d_neighbors = self.get_neighbors(node, true);
            let u_neighbors = self.get_neighbors(node, false);

            let node_index = self.node_to_index(node);

            for dn in d_neighbors {
                let dn_index = self.node_to_index(*dn);
                debug_assert_eq!(self.adjacency_matrix.get(node_index, dn_index), 1, "Directed neighbors map contains erroneous entry")
            }

            for un in u_neighbors {
                let un_index = self.node_to_index(*un);
                
                // We check to see if there is an edge (in any direction) between node and un
                debug_assert!( 
                    self.adjacency_matrix.get(node_index, un_index) == 1 || 
                    self.adjacency_matrix.get(un_index, node_index) == 1,
                    "Undirected neighbors map contains erroneous entry"
                )
            }
        }

        // Now make sure that every edge in adjacency_matrix is indeed 
        // represented in the neighbors maps.
        for u in self.node_set() {
            let u_index = self.node_to_index(u);

            for v in self.node_set() {
                let v_index = self.node_to_index(v);

                if self.adjacency_matrix.get(u_index, v_index) == 1 {
                    debug_assert!(self.get_neighbors(u, true).contains(&v), "Directed neighbors map missing entry");

                    debug_assert!(self.get_neighbors(u, false).contains(&v), "Undirected neighbors map missing entry");
                    debug_assert!(self.get_neighbors(v, false).contains(&u), "Undirected neighbors map missing entry");
                }
            }
        }

        // Make sure that the weigh matrix actually makes sense given the 
        // adjacency matrix. Make sure that if an edge has a nonzero weight,
        // then it exists according to the adjacency matrix.

        // TODO: Do invariant check on weight matrix

        // Make sure the edge sets are well-formed
        
        // TODO: Do invariant check on edge sets

    }

    // MARK: Initializers
    pub fn new() -> Graph<Node, W> {
        let g = Graph { 
            adjacency_matrix: Matrix::new(0, 0), 
            weight_matrix: Matrix::new(0, 0), 
            num_nodes: 0, 
            index_to_node_map: HashMap::new(), 
            node_to_index_map: HashMap::new(), 
            directed_neighbors_map: HashMap::new(), 
            undirected_neighbors_map: HashMap::new(), 
            directed_edge_set: HashSet::new(), 
            undirected_edge_set: HashSet::new(), 
        };

        if cfg!(debug_assertions) {
            g.check_invariant();
        }

        g
    }

    // MARK: Graph Readers

    /// Return a vector of neighbors of a given node `v`.
    /// 
    /// Crashes if `v` is not in the node set.
    pub fn get_neighbors(&self, v: Node, directed: bool) -> &Vec<Node> {
        let neighbor_map = if directed {
            &self.directed_neighbors_map
        } else {
            &self.undirected_neighbors_map
        };

        neighbor_map.get(&v).unwrap()
    }

    /// Returns the set of nodes in this graph
    pub fn node_set(&self) -> HashSet<Node> {
        self.node_to_index_map.keys().copied().collect()
    }

    /// Returns a set of all edges in this graph
    pub fn edge_set(&self, directed: bool) -> &HashSet<(Node, Node)> {
        if directed {
            &self.directed_edge_set
        } else {
            &self.undirected_edge_set
        }
    }

    // MARK: Graph Utility

    /// Adds a new node, and returns `true` if the node was added successfully.
    /// 
    /// If the node already exists, then no new node is added, and the graph is 
    /// unchanged. 
    pub fn add_node(&mut self, v: Node) -> bool {
        if self.node_set().contains(&v) {
            return false;
        }

        self.adjacency_matrix.append_col(vec![0 ; self.num_nodes]);
        self.adjacency_matrix.append_row(vec![0 ; self.num_nodes + 1]);

        self.weight_matrix.append_col(vec![W::zero() ; self.num_nodes]);
        self.weight_matrix.append_row(vec![W::zero() ; self.num_nodes + 1]);

        let new_node_index = self.num_nodes;

        self.num_nodes += 1;

        self.index_to_node_map.insert(new_node_index, v);
        self.node_to_index_map.insert(v, new_node_index);

        self.directed_neighbors_map.insert(v, Vec::new());
        self.undirected_neighbors_map.insert(v, Vec::new());

        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        true
    }

    // MARK: Printing

    /// Writes `items` as a set, like `{ a, b, c }`, or `{ }` if there are none.
    /// 
    /// Used by this graph's `Display` and `Debug` implementations.
    fn write_set<T: fmt::Display>(f: &mut fmt::Formatter<'_>, items: impl IntoIterator<Item = T>) -> fmt::Result {
        write!(f, "{{")?;

        for (i, item) in items.into_iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }

            write!(f, " {}", item)?;
        }

        write!(f, " }}")
    }

}

impl<Node: NodeType + fmt::Display, W: PoRing + fmt::Display> fmt::Display for Graph<Node, W> {

    /// Displays this graph as an adjacency list, with one line per node:
    /// 
    /// ```text
    /// u : { v, (w, 4) }
    /// ```
    /// 
    /// Each line lists the nodes that `u` has an edge to, in insertion order.
    /// An edge with a nonzero weight is shown as `(neighbor, weight)`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for index in 0..self.num_nodes {
            let node = self.index_to_node(index);

            write!(f, "{} : ", node)?;

            Self::write_set(f, self.get_neighbors(node, true).iter().map(|neighbor| {
                let weight = self.weight_matrix.get(index, self.node_to_index(*neighbor));

                if weight.is_zero() {
                    neighbor.to_string()
                } else {
                    format!("({}, {})", neighbor, weight)
                }
            }))?;

            writeln!(f)?;
        }

        Ok(())
    }
}

impl<Node: NodeType + fmt::Display, W: PoRing + fmt::Display> fmt::Debug for Graph<Node, W> {

    /// Shows the adjacency list of [`fmt::Display`], followed by this graph's
    /// internal representation: the adjacency and weight matrices, and the
    /// node <-> index maps.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)?;

        // `Matrix`'s own `Debug` opens with a newline, so each matrix lands 
        // just underneath its label.
        writeln!(f, "\nadjacency matrix:{:?}\n", self.adjacency_matrix)?;
        writeln!(f, "weight matrix:{:?}\n", self.weight_matrix)?;

        // Each map is read out of its own entries, rather than by walking one 
        // through the other, so that any disagreement between the two shows up 
        // here. Sorting by index keeps the output deterministic.
        let mut index_to_node: Vec<(usize, Node)> = self.index_to_node_map.iter().map(|(i, v)| (*i, *v)).collect();
        index_to_node.sort_by_key(|(index, _)| *index);

        let mut node_to_index: Vec<(Node, usize)> = self.node_to_index_map.iter().map(|(v, i)| (*v, *i)).collect();
        node_to_index.sort_by_key(|(_, index)| *index);

        write!(f, "index -> node: ")?;
        Self::write_set(f, index_to_node.iter().map(|(index, node)| format!("{} -> {}", index, node)))?;

        write!(f, "\nnode -> index: ")?;
        Self::write_set(f, node_to_index.iter().map(|(node, index)| format!("{} -> {}", node, index)))?;

        writeln!(f)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_inits() {
        let mut g = Graph::<usize, i32>::new();

        g.add_node(0);

        println!("{}", g);
    }

    #[test]
    fn test_display() {
        let mut g = Graph::<usize, i32>::new();

        for v in 0..3 {
            g.add_node(v);
        }

        assert_eq!(g.to_string(), "0 : { }\n1 : { }\n2 : { }\n");
    }

    #[test]
    fn test_debug() {
        let mut g = Graph::<usize, i32>::new();

        for v in 0..3 {
            g.add_node(v);
        }

        println!("{}", g);
        println!("{:?}", g);
    }
}