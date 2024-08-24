//! Adapter for graphs to have a unique exit node.
//!
//! The [`ExitConsolidator`] will record all original exit nodes in the graph,
//! and add a synthetic exit node to the graph. The synthetic exit node will be
//! the successor of all original exit nodes.

use alloc::vec::Vec;

use crate::core::graph::traversal::Dfs;
use crate::core::graph::{ControlFlowGraph, Entry, Exit, Graph, Preds, Succs};

/// An adapter for nodes in the [`ExitConsolidator`].
///
/// # Type Parameters
///
/// - `N`: The node type of the original graph.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum ConsolidatedNode<N> {
    /// A node in the original graph.
    Original(N),
    /// The synthetic exit node.
    SyntheticExit,
}

/// The adapter for the graph to have a unique exit node.
///
/// # Lifetimes
///
/// - `g`: The lifetime of the original graph.
///
/// # Type Parameters
///
/// - `G`: The original graph type.
pub struct ExitConsolidator<'g, G>
where
    G: Graph,
{
    /// The original graph.
    graph: &'g G,
    /// The exit nodes in the original graph.
    exits: Vec<G::Node>,
}

impl<'g, G> ExitConsolidator<'g, G>
where
    G: Graph + Succs + Entry,
{
    /// Create a new unique exit adapter for the given graph.
    ///
    /// The old exit nodes will be gathered during the construction. All the
    /// nodes that have no successors will be considered as exit nodes.
    ///
    /// # Parameters
    ///
    /// - `graph`: The original graph.
    pub fn new(graph: &'g G) -> Self {
        let mut dfs = Dfs::default();
        let exits = dfs
            .preorder_iter(graph)
            .filter(|&n| graph.succs(n).into_iter().next().is_none())
            .collect();
        Self { graph, exits }
    }
}

impl<'g, G> Graph for ExitConsolidator<'g, G>
where
    G: Graph,
{
    type Node = ConsolidatedNode<G::Node>;

    fn is_empty(&self) -> bool { self.graph.is_empty() }
}

impl<'g, G> Preds for ExitConsolidator<'g, G>
where
    G: Preds,
{
    fn preds(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        let mut preds = Vec::new();
        match node {
            ConsolidatedNode::Original(node) => preds.extend(
                self.graph
                    .preds(node)
                    .into_iter()
                    .map(ConsolidatedNode::Original),
            ),
            ConsolidatedNode::SyntheticExit => {
                preds.extend(self.exits.iter().copied().map(ConsolidatedNode::Original))
            }
        }
        preds
    }
}

impl<'g, G> Succs for ExitConsolidator<'g, G>
where
    G: Succs,
{
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        let mut succs = Vec::new();
        match node {
            ConsolidatedNode::Original(node) => {
                succs.extend(
                    self.graph
                        .succs(node)
                        .into_iter()
                        .map(ConsolidatedNode::Original),
                );
                // The `exits` is expected to be small, so `contains` should not be a
                // performance issue.
                if self.exits.contains(&node) {
                    // If the given node is an old exit, concatenate the new exit node.
                    succs.push(ConsolidatedNode::SyntheticExit);
                }
            }
            // No successors for the exit node.
            ConsolidatedNode::SyntheticExit => {}
        }
        succs
    }
}

impl<'g, G> Entry for ExitConsolidator<'g, G>
where
    G: Entry,
{
    fn entry(&self) -> Option<Self::Node> { self.graph.entry().map(ConsolidatedNode::Original) }
}

impl<'g, G> ControlFlowGraph for ExitConsolidator<'g, G> where G: ControlFlowGraph {}

impl<'g, G> Exit for ExitConsolidator<'g, G>
where
    G: ControlFlowGraph,
{
    fn exit(&self) -> Option<Self::Node> {
        // The `exits` can be empty when the graph is not empty, so we need to check
        // the graph.
        if self.graph.is_empty() {
            None
        } else {
            Some(ConsolidatedNode::SyntheticExit)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::graph::adapters::TestCFG;

    #[test]
    fn test_unique_exit_adapter() {
        let graph = TestCFG::new(0, &[(0, 1), (1, 2), (1, 3)]);
        let adapter = ExitConsolidator::new(&graph);

        assert_eq!(adapter.exit(), Some(ConsolidatedNode::SyntheticExit));
        assert_eq!(adapter.entry(), Some(ConsolidatedNode::Original(0)));

        assert_eq!(
            adapter
                .succs(ConsolidatedNode::Original(0))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(1)]
        );
        assert_eq!(
            adapter
                .succs(ConsolidatedNode::Original(1))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(2), ConsolidatedNode::Original(3),]
        );
        assert_eq!(
            adapter
                .succs(ConsolidatedNode::Original(2))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::SyntheticExit,]
        );
        assert_eq!(
            adapter
                .succs(ConsolidatedNode::Original(3))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::SyntheticExit,]
        );
        assert_eq!(
            adapter
                .succs(ConsolidatedNode::SyntheticExit)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::Original(0))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::Original(1))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(0)]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::Original(2))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(1)]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::Original(3))
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(1)]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::SyntheticExit)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![ConsolidatedNode::Original(3), ConsolidatedNode::Original(2),]
        );

        assert!(!adapter.is_empty());
    }

    #[test]
    fn test_unique_exit_empty() {
        let graph = TestCFG::empty();
        let adapter = ExitConsolidator::new(&graph);

        assert_eq!(adapter.exit(), None);
        assert_eq!(adapter.entry(), None);
        assert_eq!(
            adapter
                .succs(ConsolidatedNode::SyntheticExit)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            adapter
                .preds(ConsolidatedNode::SyntheticExit)
                .into_iter()
                .collect::<Vec<_>>(),
            vec![]
        );
        assert!(adapter.is_empty());
    }
}
