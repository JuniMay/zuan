//! Control Dependence Graph.

use alloc::vec::Vec;
use core::hash::Hash;

use crate::core::graph::adapters::Reverse;
use crate::core::graph::dominance::{DomTree, DominanceFrontierInfo};
use crate::core::graph::traversal::Dfs;
use crate::core::graph::{ControlFlowGraph, Exit, Graph, Succs};
use crate::HashMap;

/// A control dependence graph.
///
/// # Type Parameters
///
/// - `N`: The node type of the control flow graph.
pub struct ControlDependenceGraph<N> {
    cdg: HashMap<N, Vec<N>>,
    valid: bool,
}

impl<N> Default for ControlDependenceGraph<N> {
    fn default() -> Self {
        Self {
            cdg: HashMap::default(),
            valid: false,
        }
    }
}

impl<N> ControlDependenceGraph<N>
where
    N: Copy + Eq + Hash,
{
    /// Check if the control dependence graph is valid.
    pub fn is_valid(&self) -> bool { self.valid }

    /// Clear and invalidate the control dependence graph.
    pub fn clear(&mut self) {
        self.cdg.clear();
        self.valid = false;
    }

    /// Invalidate the control dependence graph.
    pub fn invalidate(&mut self) {
        self.clear();
        self.valid = false;
    }

    /// Compute the control dependence graph from a control flow graph and a
    /// post-dominator tree.
    ///
    /// # Parameters
    ///
    /// - `graph`: The original control flow graph.
    /// - `post_domtree`: A dominator tree instance to hold the post-dominator
    ///   tree, which will be invalidated and recomputed from the reverse CFG.
    pub fn compute<G, D>(&mut self, graph: &G, post_domtree: &mut D)
    where
        G: ControlFlowGraph<Node = N> + Exit,
        D: DomTree<Node = N>,
    {
        if self.is_valid() {
            return;
        }

        let reversed = Reverse::new(graph);

        let mut dfs = Dfs::default();
        let mut post_df = DominanceFrontierInfo::default();
        post_domtree.invalidate();

        let postorder = dfs.postorder_iter(&reversed).collect::<Vec<_>>();

        post_domtree.compute(&reversed);
        post_df.compute(&reversed, post_domtree, &postorder);

        self.compute_from_df(&post_df, &postorder);
    }

    /// Compute the control dependence graph from a computed dominance frontier.
    ///
    /// If the post-dominator tree is not computed yet, consider using
    /// [`Self::compute`] instead.
    ///
    /// The construction method is referenced from *Modern Compiler
    /// Implementation in C*, Chapter 19.
    ///
    /// # Parameters
    ///
    /// - `post_df`: The computed dominance frontier of the reversed CFG.
    /// - `nodes`: The nodes in the control flow graph.
    pub fn compute_from_df(&mut self, post_df: &DominanceFrontierInfo<N>, nodes: &[N])
    where
        N: Copy + Eq + Hash,
    {
        if self.is_valid() {
            return;
        }

        for &node in nodes {
            for &frontier_node in post_df.frontier(node) {
                // The CDG has edge x -> y whenever x \in DF_G′[y].
                self.cdg.entry(frontier_node).or_default().push(node);
            }
        }

        self.valid = true;
    }
}

impl<N> Graph for ControlDependenceGraph<N>
where
    N: Copy + Eq + Hash,
{
    type Node = N;

    fn is_empty(&self) -> bool { self.cdg.is_empty() }
}

impl<N> Succs for ControlDependenceGraph<N>
where
    N: Copy + Eq + Hash,
{
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        self.cdg
            .get(&node)
            .into_iter()
            .flat_map(|succs| succs.iter().copied())
    }
}
