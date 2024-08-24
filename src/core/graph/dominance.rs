//! Algorithm for Dominance Computation

mod domtree_ext;
mod iterative;

use core::hash::Hash;

pub use domtree_ext::*;
pub use iterative::*;

use super::ControlFlowGraph;

/// Kinds of dominance between two nodes.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Dominance {
    /// The first node strictly dominates the second node.
    Strict,
    /// The first node is identical to the second node.
    Identical,
    /// The first node does not dominate the second node.
    None,
}

impl From<Dominance> for bool {
    fn from(d: Dominance) -> bool { matches!(d, Dominance::Strict | Dominance::Identical) }
}

/// A trait for dominator trees.
pub trait DomTree {
    /// The type of nodes in the dominator tree and the control flow graph.
    type Node: Copy + Eq + Hash;

    /// Interface for computing the dominator tree.
    fn compute<G>(&mut self, graph: &G)
    where
        G: ControlFlowGraph<Node = Self::Node>;

    /// Interface for checking if the dominator tree is valid.
    fn is_valid(&self) -> bool;

    /// Invalidate the dominator tree.
    fn invalidate(&mut self);

    /// Check if a node is reachable from the entry, i.e., it is in the
    /// dominator tree.
    fn is_reachable(&self, node: Self::Node) -> bool;

    /// Query the immediate dominator of a node.
    ///
    /// # Returns
    ///
    /// - `Some(idom)`: The immediate dominator of the node.
    /// - `None`: The node is unreachable or is the entry node.
    fn immediate_dominator(&self, node: Self::Node) -> Option<Self::Node>;

    /// Query the dominance relationship between two nodes.
    ///
    /// # Returns
    ///
    /// - `Some(Dominance)`: The dominance relationship between the two nodes.
    /// - `None`: Either of the nodes is unreachable or does not exist.
    fn dominance(&self, a: Self::Node, b: Self::Node) -> Option<Dominance>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::graph::adapters::TestCFG;

    #[test]
    fn test_dominance() {
        //       5
        //      / \
        //     /   \
        //    /     \
        //   4       3
        //   |       |
        //   1 <---- 2
        //   +------->
        //
        // Ref: Figure 2 in "A Simple, Fast Dominance Algorithm".

        let graph = TestCFG::new(5, &[(5, 4), (4, 1), (1, 2), (2, 1), (5, 3), (3, 2)]);
        let mut domtree = IterativeDomTree::default();
        domtree.compute(&graph);

        assert_eq!(domtree.immediate_dominator(5), None);
        assert_eq!(domtree.immediate_dominator(4), Some(5));
        assert_eq!(domtree.immediate_dominator(3), Some(5));
        assert_eq!(domtree.immediate_dominator(2), Some(5));
        assert_eq!(domtree.immediate_dominator(1), Some(5));

        assert_eq!(domtree.dominance(5, 5), Some(Dominance::Identical));
        assert_eq!(domtree.dominance(5, 4), Some(Dominance::Strict));
        assert_eq!(domtree.dominance(5, 3), Some(Dominance::Strict));
        assert_eq!(domtree.dominance(5, 2), Some(Dominance::Strict));
        assert_eq!(domtree.dominance(5, 1), Some(Dominance::Strict));

        assert_eq!(domtree.dominance(1, 2), Some(Dominance::None));
        assert_eq!(domtree.dominance(2, 1), Some(Dominance::None));

        assert!(!domtree.is_reachable(0));
    }

    #[test]
    fn test_dominance_ext() {
        let graph = TestCFG::new(5, &[(5, 4), (4, 1), (1, 2), (2, 1), (5, 3), (3, 2)]);
        let mut domtree = IterativeDomTree::default();
        let mut domtree_ext = DomTreeExt::default();
        let mut df = DominanceFrontierInfo::default();

        domtree.compute(&graph);
        domtree_ext.compute(&domtree, domtree.postorder());
        df.compute(&graph, &domtree, domtree.postorder());

        assert_eq!(domtree_ext.dominance(5, 5), Some(Dominance::Identical));
        assert_eq!(domtree_ext.dominance(5, 4), Some(Dominance::Strict));
        assert_eq!(domtree_ext.dominance(5, 3), Some(Dominance::Strict));
        assert_eq!(domtree_ext.dominance(5, 2), Some(Dominance::Strict));
        assert_eq!(domtree_ext.dominance(5, 1), Some(Dominance::Strict));

        assert_eq!(domtree_ext.dominance(1, 2), Some(Dominance::None));
        assert_eq!(domtree_ext.dominance(2, 1), Some(Dominance::None));

        assert_eq!(df.frontier(5), &[]);
        assert_eq!(df.frontier(4), &[1]);
        assert_eq!(df.frontier(3), &[2]);
        assert_eq!(df.frontier(2), &[1]);
        assert_eq!(df.frontier(1), &[2]);
    }

    #[test]
    fn test_empty() {
        let graph = TestCFG::empty();
        let mut domtree = IterativeDomTree::default();
        let mut domtree_ext = DomTreeExt::default();
        let mut df = DominanceFrontierInfo::default();

        domtree.compute(&graph);
        domtree_ext.compute(&domtree, domtree.postorder());
        df.compute(&graph, &domtree, domtree.postorder());

        assert!(!domtree.is_reachable(0));
        assert!(domtree_ext.depth(0).is_none());
    }
}
