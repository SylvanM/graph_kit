use core::fmt;
use std::{collections::{HashMap, HashSet, VecDeque}, debug_assert, debug_assert_eq, hash::Hash};

use matrix_kit::dynamic::matrix::*;
use algebra_kit::algebra::PoRing;

pub trait NodeType: Eq + Hash + Clone {}
impl<T: Eq + Hash + Clone> NodeType for T {}

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
    index_to_node_map: Vec<Node>,

    /// Internal mapping from generic nodes to node indices
    node_to_index_map: HashMap<Node, usize>,

    /// Map from a node index to the indices of its directed neighbors
    directed_neighbors_map: HashMap<usize, Vec<usize>>,

    /// Map from a node index to the indices of its undirected neighbors
    undirected_neighbors_map: HashMap<usize, Vec<usize>>,

    /// A set of all directed edges in this graph, by node index
    directed_edge_set: HashSet<(usize, usize)>,

    /// A set of all undirected edges in this graph, by node index
    undirected_edge_set: HashSet<(usize, usize)>,

}

impl<Node: NodeType, W: PoRing> Graph<Node, W> {

    fn node_to_index(&self, node: &Node) -> usize {
        *self.node_to_index_map.get(node).unwrap()
    }

    fn index_to_node(&self, index: usize) -> &Node {
        &self.index_to_node_map[index]
    }

    fn check_invariant(&self) {
        // the adjacency matrix is ground truth.

        debug_assert_eq!(self.num_nodes, self.adjacency_matrix.row_count(), "Adjacency matrix wrong height");
        debug_assert_eq!(self.num_nodes, self.adjacency_matrix.col_count(), "Adjacency matrix wrong width");

        debug_assert_eq!(self.num_nodes, self.weight_matrix.row_count(), "Weight matrix wrong height");
        debug_assert_eq!(self.num_nodes, self.weight_matrix.col_count(), "Weight matrix wrong width");

        debug_assert_eq!(self.num_nodes, self.index_to_node_map.len(), "Index -> Node map wrong size");
        debug_assert_eq!(self.num_nodes, self.node_to_index_map.keys().count(), "Node -> Index map wrong size");

        // Make sure the index mapping is total on [0, n), and that it 
        // corresponds with the node -> index mapping
        debug_assert!(
            (0..self.num_nodes).all(|i|
                match self.index_to_node_map.get(i) {
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
        for node_index in 0..self.num_nodes {
            let d_neighbors = self.directed_neighbors_map.get(&node_index).unwrap();
            let u_neighbors = self.undirected_neighbors_map.get(&node_index).unwrap();

            for &dn_index in d_neighbors {
                debug_assert_eq!(self.adjacency_matrix.get(node_index, dn_index), 1, "Directed neighbors map contains erroneous entry")
            }

            for &un_index in u_neighbors {
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
        for u_index in 0..self.num_nodes {
            for v_index in 0..self.num_nodes {
                if self.adjacency_matrix.get(u_index, v_index) == 1 {
                    debug_assert!(self.directed_neighbors_map.get(&u_index).unwrap().contains(&v_index), "Directed neighbors map missing entry");

                    debug_assert!(self.undirected_neighbors_map.get(&u_index).unwrap().contains(&v_index), "Undirected neighbors map missing entry");
                    debug_assert!(self.undirected_neighbors_map.get(&v_index).unwrap().contains(&u_index), "Undirected neighbors map missing entry");
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
            index_to_node_map: Vec::new(),
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

    /// Creates a graph of just nodes with no edges yet.
    pub fn from_nodes(nodes: &[Node]) -> Graph<Node, W> {
        let n = nodes.iter().count();

        let g = Graph {
            adjacency_matrix: Matrix::new(n, n),
            weight_matrix: Matrix::new(n, n),
            num_nodes: n,
            index_to_node_map: nodes.to_vec(),
            node_to_index_map: nodes.iter().enumerate().map(|(index, node)| (node.clone(), index)).collect(),
            directed_neighbors_map: Vec::from_iter(0..n).iter().map(|&i| (i, Vec::new())).collect(),
            undirected_neighbors_map: Vec::from_iter(0..n).iter().map(|&i| (i, Vec::new())).collect(),
            directed_edge_set: HashSet::new(),
            undirected_edge_set: HashSet::new(),
        };

        if cfg!(debug_assertions) {
            g.check_invariant();
        }

        g
    }

    // MARK: Graph Readers

    /// The number of nodes in this graph
    pub fn num_nodes(&self) -> usize {
        self.num_nodes
    }

    /// Return a vector of neighbors of a given node `v`.
    /// 
    /// Crashes if `v` is not in the node set.
    pub fn get_neighbors(&self, v: &Node, directed: bool) -> Vec<&Node> {
        let neighbor_map = if directed {
            &self.directed_neighbors_map
        } else {
            &self.undirected_neighbors_map
        };

        neighbor_map.get(&self.node_to_index(v)).unwrap()
            .iter()
            .map(|&index| self.index_to_node(index))
            .collect()
    }

    /// Returns `true` if the node set contains a particular node
    pub fn contains(&self, v: &Node) -> bool {
        self.node_to_index_map.contains_key(v)
    }

    /// Returns the set of nodes in this graph
    pub fn node_set(&self) -> HashSet<&Node> {
        self.node_to_index_map.keys().collect()
    }

    /// Returns a set of all edges in this graph
    pub fn edge_set(&self, directed: bool) -> HashSet<(&Node, &Node)> {
        let edge_set = if directed {
            &self.directed_edge_set
        } else {
            &self.undirected_edge_set
        };

        edge_set.iter()
            .map(|&(u, v)| (self.index_to_node(u), self.index_to_node(v)))
            .collect()
    }

    // MARK: Graph Utility

    /// Adds a new node, and returns `true` if the node was added successfully.
    /// 
    /// If the node already exists, then no new node is added, and the graph is 
    /// unchanged. 
    pub fn add_node(&mut self, v: Node) -> bool {
        if self.contains(&v) {
            return false;
        }

        self.adjacency_matrix.append_col(vec![0 ; self.num_nodes]);
        self.adjacency_matrix.append_row(vec![0 ; self.num_nodes + 1]);

        self.weight_matrix.append_col(vec![W::zero() ; self.num_nodes]);
        self.weight_matrix.append_row(vec![W::zero() ; self.num_nodes + 1]);

        let new_node_index = self.num_nodes;

        self.num_nodes += 1;

        self.index_to_node_map.push(v.clone());
        self.node_to_index_map.insert(v, new_node_index);

        self.directed_neighbors_map.insert(new_node_index, Vec::new());
        self.undirected_neighbors_map.insert(new_node_index, Vec::new());

        if cfg!(debug_assertions) {
            self.check_invariant();
        }

        true
    }

    /// Connects a node to one other node
    ///
    /// If either node does not already exist, it is created.
    ///
    /// Inserting an edge that is already present leaves the graph unchanged.
    pub fn insert_edge(&mut self, u: &Node, v: &Node) {
        if !self.contains(u) {
            self.add_node(u.clone());
        }

        if !self.contains(v) {
            self.add_node(v.clone());
        }

        let u_index = self.node_to_index(u);
        let v_index = self.node_to_index(v);

        if self.adjacency_matrix.get(u_index, v_index) == 1 {
            return;
        }

        self.adjacency_matrix.set(u_index, v_index, 1);

        self.directed_edge_set.insert((u_index, v_index));
        self.directed_neighbors_map.get_mut(&u_index).unwrap().push(v_index);

        if !self.undirected_edge_set.contains(&(v_index, u_index)) {
            self.undirected_edge_set.insert((u_index, v_index));

            self.undirected_neighbors_map.get_mut(&u_index).unwrap().push(v_index);

            if u_index != v_index {
                self.undirected_neighbors_map.get_mut(&v_index).unwrap().push(u_index);
            }
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
    }

    /// Connects a node to a set of neighbors
    /// 
    /// If a node does not already exist, the node is just created
    pub fn insert_edges(&mut self, v: &Node, neighbors: &[Node]) {
        for u in neighbors {
            self.insert_edge(v, u);
        }
    }

    /// Adds a set of nodes and edges between all pairs of them. 
    /// 
    /// If we are given nodes v1, ... vn, then there will be 
    /// an edge (v_i, v_j) for all i < j. (That is, each node will have a 
    /// directed edge pointing to all nodes coming after it.)
    /// 
    /// If you want a self-loop, you can give duplicate nodes.
    pub fn insert_connected_component(&mut self, connected_nodes: &[Node]) {
        let mut rest = connected_nodes;

        if let Some(first) = connected_nodes.first() {
            self.add_node(first.clone());
        }

        while let [v, remaining @ ..] = rest {
            self.insert_edges(v, remaining);
            rest = remaining;
        }

        if cfg!(debug_assertions) {
            self.check_invariant();
        }
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

// MARK: BFS Infra

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IndexBFSStep {
    node: usize,
    parent: Option<usize>, // node that discovered this one
    depth: usize,
}

/// A breadth-first traversal over node indices.
/// 
/// This is the underlying BFS functionality, all BFS-related tasks can 
/// use this.
struct IndexBFS<'g, Node: NodeType, W: PoRing> {
    graph: &'g Graph<Node, W>,
    directed: bool,

    /// Discovered nodes waiting to be visited, as `(node, parent)` pairs
    queue: VecDeque<(usize, Option<usize>)>,

    /// The depth of each node, or `None` if it hasn't been discovered yet
    depths: Vec<Option<usize>>,
}

impl<'g, Node: NodeType, W: PoRing> IndexBFS<'g, Node, W> {

    /// Creates a traversal with no sources.
    fn new(graph: &'g Graph<Node, W>, directed: bool) -> IndexBFS<'g, Node, W> {
        IndexBFS {
            graph,
            directed,
            queue: VecDeque::new(),
            depths: vec![None ; graph.num_nodes],
        }
    }

    /// Adds a source at depth 0, unless it has already been discovered.
    fn push_source(&mut self, index: usize) {
        if self.depths[index].is_none() {
            self.depths[index] = Some(0);
            self.queue.push_back((index, None));
        }
    }

    /// The depth of a node, or `None` if it hasn't been discovered yet.
    fn depth(&self, index: usize) -> Option<usize> {
        self.depths[index]
    }

}

impl<Node: NodeType, W: PoRing> Iterator for IndexBFS<'_, Node, W> {
    type Item = IndexBFSStep;

    fn next(&mut self) -> Option<IndexBFSStep> {
        let (node, parent) = self.queue.pop_front()?;
        let depth = self.depths[node].unwrap();

        let neighbors_map = if self.directed {
            &self.graph.directed_neighbors_map
        } else {
            &self.graph.undirected_neighbors_map
        };

        for &neighbor in &neighbors_map[&node] {
            if self.depths[neighbor].is_none() {
                self.depths[neighbor] = Some(depth + 1);
                self.queue.push_back((neighbor, Some(node)));
            }
        }

        Some(IndexBFSStep { node, parent, depth })
    }
}

/// A single node visited by a [`BFS`], along with the node it was discovered
/// from and its distance from the sources.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BFSStep<'g, Node> {
    pub node: &'g Node,
    pub parent: Option<&'g Node>,
    pub depth: usize,
}

/// A breadth-first traversal of a graph, yielding a [`BFSStep`] for each node
/// reachable from its sources, in order of nondecreasing depth.
///
/// Create one with [`Graph::bfs`].
pub struct BFS<'g, Node: NodeType, W: PoRing> {
    index_bfs: IndexBFS<'g, Node, W>,
}

impl<Node: NodeType, W: PoRing> BFS<'_, Node, W> {

    /// Adds another source at depth 0, unless it has already been discovered.
    ///
    /// To keep depths as true distances, only add sources before iterating,
    /// or once the traversal has run out.
    ///
    /// Crashes if `v` is not in the node set.
    pub fn push_source(&mut self, v: &Node) {
        let index = self.index_bfs.graph.node_to_index(v);
        self.index_bfs.push_source(index);
    }

    /// The depth of `v`, or `None` if it hasn't been discovered yet.
    ///
    /// Crashes if `v` is not in the node set.
    pub fn depth(&self, v: &Node) -> Option<usize> {
        self.index_bfs.depth(self.index_bfs.graph.node_to_index(v))
    }
}

impl<'g, Node: NodeType, W: PoRing> Iterator for BFS<'g, Node, W> {
    type Item = BFSStep<'g, Node>;

    fn next(&mut self) -> Option<BFSStep<'g, Node>> {
        let graph = self.index_bfs.graph;
        let step = self.index_bfs.next()?;

        Some(BFSStep {
            node: graph.index_to_node(step.node),
            parent: step.parent.map(|parent| graph.index_to_node(parent)),
            depth: step.depth,
        })
    }
}

impl<Node: NodeType, W: PoRing> Graph<Node, W> {

    /// Starts a breadth-first traversal from `start`. More sources can be
    /// added with [`BFS::push_source`].
    ///
    /// Crashes if `start` is not in the node set.
    pub fn bfs(&self, start: &Node, directed: bool) -> BFS<'_, Node, W> {
        let mut index_bfs = IndexBFS::new(self, directed);
        index_bfs.push_source(self.node_to_index(start));

        BFS { index_bfs }
    }

    /// Computes a BFS coloring of the graph
    /// 
    /// Returns three objects:
    ///     (1) A Vec<Vec<Node>> which is a list of each BFS layer in increasing
    ///         distance from the source, 
    ///     (2) A Vec<Node which represents the set of all unreachable nodes, and
    ///     (3) A HashMap<Node, Option(usize)> which is a coloring of all nodes
    ///         of their distances, where None represents unreachable.
    /// 
    /// (1)+(2) together carries the same information as (3), but they are
    /// in some sense transposes of each other, depends on what way you plan 
    /// on using the data. Same effort to compute so might as well compute both.
    pub fn bfs_coloring(&self, start: &Node, directed: bool) -> (
        Vec<Vec<Node>>, Vec<Node>, HashMap<Node, Option<usize>>
    ) {
        let mut index_bfs = IndexBFS::new(self, directed);
        index_bfs.push_source(self.node_to_index(start));

        // Steps come out in nondecreasing depth, so each new depth starts a new layer
        let mut layers: Vec<Vec<Node>> = Vec::new();
        for step in index_bfs.by_ref() {
            if step.depth == layers.len() {
                layers.push(Vec::new());
            }
            layers[step.depth].push(self.index_to_node(step.node).clone());
        }

        // The main BFS stuff is done by this point, now we just do sillyness.

        let mut unreachable: Vec<Node> = Vec::new();
        let mut coloring: HashMap<Node, Option<usize>> = HashMap::new();
        for index in 0..self.num_nodes {
            let node = self.index_to_node(index).clone();
            let depth = index_bfs.depth(index);

            if depth.is_none() {
                unreachable.push(node.clone());
            }
            coloring.insert(node, depth);
        }

        (layers, unreachable, coloring)
    }

    /// Returns a BFS sub-tree of the graph, starting from some root.
    /// 
    /// Weights are dropped, this is only really used for connectivity
    /// and un-weighted distance stuff.
    pub fn bfs_tree(&self, start: &Node, directed: bool) -> Graph<Node> {
        let mut tree = Graph::new();
        tree.add_node(start.clone());

        // Each node gets an edge from the node that discovered it
        for step in self.bfs(start, directed) {
            if let Some(parent) = step.parent {
                tree.insert_edge(parent, step.node);
            }
        }

        tree
    }

    /// Computes connected components of the graph.
    pub fn connected_components(&self) -> Vec<Vec<Node>> {
        let mut connected_components = Vec::new();
        let mut frontier = self.node_set();

        while let Some(&start) = frontier.iter().next() {
            let (layers, _, _) = self.bfs_coloring(start, false);
            let component: Vec<Node> = layers.into_iter().flatten().collect();

            for v in &component {
                frontier.remove(v);
            }
            
            connected_components.push(component);
        }

        connected_components
    }

}

// MARK: Debugging

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

            Self::write_set(f, self.directed_neighbors_map.get(&index).unwrap().iter().map(|&neighbor_index| {
                let neighbor = self.index_to_node(neighbor_index);
                let weight = self.weight_matrix.get(index, neighbor_index);

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
        let index_to_node: Vec<(usize, &Node)> = self.index_to_node_map.iter().enumerate().collect();

        let mut node_to_index: Vec<(&Node, usize)> = self.node_to_index_map.iter().map(|(v, i)| (v, *i)).collect();
        node_to_index.sort_by_key(|(_, index)| *index);

        write!(f, "index -> node: ")?;
        Self::write_set(f, index_to_node.iter().map(|(index, node)| format!("{} -> {}", index, node)))?;

        write!(f, "\nnode -> index: ")?;
        Self::write_set(f, node_to_index.iter().map(|(node, index)| format!("{} -> {}", node, index)))?;

        writeln!(f)
    }
}

// MARK: Tests

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
    fn test_debug() {
        let mut g = Graph::<usize, i32>::new();

        for v in 0..3 {
            g.add_node(v);
        }

        println!("{}", g);
        println!("{:?}", g);
    }

    // MARK: Claude's Tests.

    /// The path 0 -> 1 -> 2 -> 3, plus an isolated node 4
    fn path_graph() -> Graph<usize, i32> {
        let mut g = Graph::new();

        g.insert_edge(&0, &1);
        g.insert_edge(&1, &2);
        g.insert_edge(&2, &3);
        g.add_node(4);

        g
    }

    #[test]
    fn test_bfs_path() {
        let g = path_graph();
        let mut bfs = g.bfs(&0, true);

        let steps: Vec<(usize, Option<usize>, usize)> = bfs.by_ref()
            .map(|step| (*step.node, step.parent.copied(), step.depth))
            .collect();

        assert_eq!(steps, vec![(0, None, 0), (1, Some(0), 1), (2, Some(1), 2), (3, Some(2), 3)]);
        assert_eq!(bfs.depth(&3), Some(3));
        assert_eq!(bfs.depth(&4), None);
    }

    #[test]
    fn test_bfs_directed_vs_undirected() {
        let g = path_graph();

        assert_eq!(g.bfs(&3, true).count(), 1);
        assert_eq!(g.bfs(&3, false).map(|step| step.depth).collect::<Vec<_>>(), vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_bfs_diamond() {
        let mut g = Graph::<usize, i32>::new();
        g.insert_edges(&0, &[1, 2]);
        g.insert_edge(&1, &3);
        g.insert_edge(&2, &3);

        let steps: Vec<BFSStep<usize>> = g.bfs(&0, true).collect();

        assert_eq!(steps.len(), 4);
        assert_eq!(steps[3], BFSStep { node: &3, parent: Some(&1), depth: 2 });
    }

    #[test]
    fn test_bfs_multi_source() {
        let g = path_graph();
        let mut bfs = g.bfs(&0, false);
        bfs.push_source(&3);

        let depths: HashMap<usize, usize> = bfs.by_ref().map(|step| (*step.node, step.depth)).collect();

        assert_eq!(depths, HashMap::from([(0, 0), (3, 0), (1, 1), (2, 1)]));

        // Once exhausted, a new source starts a fresh component
        bfs.push_source(&4);
        assert_eq!(bfs.next(), Some(BFSStep { node: &4, parent: None, depth: 0 }));
        assert_eq!(bfs.next(), None);
    }

    #[test]
    fn test_bfs_tree_layers() {
        // A diamond with a tail, a cycle back to the root, and a separate component
        let mut g = Graph::<usize, i32>::new();
        g.insert_edges(&0, &[1, 2]);
        g.insert_edge(&1, &3);
        g.insert_edge(&2, &3);
        g.insert_edge(&3, &4);
        g.insert_edge(&4, &0);
        g.insert_edge(&5, &6);

        for root in [0, 3, 5] {
            let tree = g.bfs_tree(&root);
            let (layers, _, _) = g.bfs_coloring(&root, false);
            let (tree_layers, tree_unreachable, _) = tree.bfs_coloring(&root, true);

            assert_eq!(tree_layers, layers);
            assert!(tree_unreachable.is_empty());

            // A tree has exactly one fewer edge than it has nodes
            assert_eq!(tree.edge_set(true).len() + 1, tree.num_nodes());
        }
    }

}