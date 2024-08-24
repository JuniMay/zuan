//! Adapter to reverse graphs.

use crate::core::graph::{ControlFlowGraph, Edges, Entry, Exit, Graph, Preds, Succs};

/// An adapter for the graph to reverse the edges.
///
/// # Lifetimes
///
/// - `g`: The lifetime of the original graph.
///
/// # Type Parameters
///
/// - `G`: The original graph type.
pub struct Reverse<'g, G> {
    graph: &'g G,
}

impl<'g, G> Reverse<'g, G> {
    /// Create a new reverse adapter for the given graph.
    ///
    /// # Parameters
    ///
    /// - `graph`: The original graph.
    pub fn new(graph: &'g G) -> Self { Self { graph } }
}

impl<'g, G> Graph for Reverse<'g, G>
where
    G: Graph,
{
    type Node = G::Node;

    fn is_empty(&self) -> bool { self.graph.is_empty() }
}

impl<'g, G> Preds for Reverse<'g, G>
where
    G: Succs,
{
    fn preds(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        self.graph.succs(node)
    }
}

impl<'g, G> Succs for Reverse<'g, G>
where
    G: Preds,
{
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        self.graph.preds(node)
    }
}

impl<'g, G> Entry for Reverse<'g, G>
where
    G: Exit,
{
    fn entry(&self) -> Option<Self::Node> { self.graph.exit() }
}

impl<'g, G> Exit for Reverse<'g, G>
where
    G: Entry,
{
    fn exit(&self) -> Option<Self::Node> { self.graph.entry() }
}

impl<'g, G> Edges for Reverse<'g, G>
where
    G: Edges,
{
    type Edge = G::Edge;

    fn edges(&self, src: Self::Node, dst: Self::Node) -> impl IntoIterator<Item = &Self::Edge> {
        self.graph.edges(dst, src)
    }
}

impl<'g, G> ControlFlowGraph for Reverse<'g, G> where G: ControlFlowGraph + Exit {}
