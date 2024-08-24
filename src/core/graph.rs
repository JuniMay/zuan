//! Graph Data Structure

use core::hash::Hash;

#[cfg(feature = "fuzzing")]
pub mod fuzzing;

pub mod adapters;
mod control_dependence;
pub mod dominance;
pub mod traversal;

/// A graph.
pub trait Graph {
    /// The type of nodes in the graph.
    ///
    /// Nodes should just be a lightweight handle/key to the actual data.
    /// Typically, the node can be an [`Idx`](crate::core::utils::Idx) or an
    /// [`ArenaPtr`](crate::core::storage::ArenaPtr).
    type Node: Copy + Eq + Hash;

    /// Check if the graph is empty.
    fn is_empty(&self) -> bool;
}

/// A directed graph with predecessors (incoming edges).
pub trait Preds: Graph {
    /// Get an iterator over the predecessors of a node.
    fn preds(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node>;
}

/// A directed graph with successors (outgoing edges).
pub trait Succs: Graph {
    /// Get an iterator over the successors of a node.
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node>;
}

/// A directed graph with a single entry node.
pub trait Entry: Graph {
    /// Get the entry node.
    ///
    /// The entry node should not be [`None`] as long as [`Graph::is_empty`] is
    /// [`false`].
    fn entry(&self) -> Option<Self::Node>;
}

/// A graph with edges.
pub trait Edges: Graph {
    /// The type of edge data.
    type Edge;

    /// Get the edge data between two nodes.
    ///
    /// There can be multiple edges between two nodes, so this method returns an
    /// iterator.
    fn edges(&self, src: Self::Node, dst: Self::Node) -> impl IntoIterator<Item = &Self::Edge>;
}

/// A graph that can iterate over all adjacent nodes, typically used for
/// undirected graphs.
pub trait Adjacent: Graph {
    /// Get an iterator over all adjacent nodes of a node.
    fn adjacent(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node>;
}

/// A control flow graph.
///
/// A control flow graph is a directed graph with an entry node, predecessors,
/// and successors.
///
/// Note that we do not restrict the control flow graph to have a single exit
/// node, as the machine code may have multiple exit points.
pub trait ControlFlowGraph: Graph + Entry + Preds + Succs {}

/// A directed graph with a single exit node.
pub trait Exit: Graph {
    /// Get the unique exit node.
    ///
    /// The exit node should not be [`None`] as long as [`Graph::is_empty`] is
    /// [`false`].
    fn exit(&self) -> Option<Self::Node>;
}
