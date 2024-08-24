//! Extended dominator tree with additional information.
//!
//! This module provides the dominance frontier information and the extended
//! dominator tree. The [`DominanceFrontierInfo`] can be computed from a control
//! flow graph, its dominator tree and a corresponding post-order sequence. The
//! [`DomTreeExt`] is an extension of the dominator tree with additional node
//! information, which enables fast dominance query and traversal on the tree.

use alloc::vec::Vec;
use core::hash::Hash;
use core::mem;

use super::{DomTree, Dominance};
use crate::core::graph::traversal::{Dfs, TraversalIdx};
use crate::core::graph::{ControlFlowGraph, Graph, Succs};
use crate::core::utils::Reserved;
use crate::HashMap;

/// Information of dominance frontiers.
///
/// # Type Parameters
///
/// - `N`: The node type of the control flow graph.
pub struct DominanceFrontierInfo<N> {
    /// The frontier storage.
    frontiers: HashMap<N, Vec<N>>,
    /// If this info is valid.
    valid: bool,
}

impl<N> Default for DominanceFrontierInfo<N> {
    fn default() -> Self {
        Self {
            frontiers: HashMap::default(),
            valid: false,
        }
    }
}

impl<N> DominanceFrontierInfo<N> {
    /// Check if this info is valid.
    pub fn is_valid(&self) -> bool { self.valid }

    /// Invalidate this info.
    pub fn invalidate(&mut self) {
        self.frontiers.clear();
        self.valid = false;
    }

    /// Query the frontier of a node.
    pub fn frontier(&self, node: N) -> &[N]
    where
        N: Copy + Eq + Hash,
    {
        self.frontiers.get(&node).map_or(&[], |f| f)
    }

    /// Compute the dominance frontiers.
    ///
    /// # Parameters
    ///
    /// - `graph`: The control flow graph.
    /// - `domtree`: The dominator tree of the control flow graph.
    /// - `postorder`: The post-order sequence of the control flow graph.
    ///
    /// # Panics
    ///
    /// - Panics if the dominator tree is invalid.
    /// - Panics if a node in the post-order sequence is unreachable.
    pub fn compute<G, D>(&mut self, graph: &G, domtree: &D, postorder: &[N])
    where
        G: ControlFlowGraph<Node = N>,
        D: DomTree<Node = N>,
        N: Copy + Eq + Hash,
    {
        assert!(domtree.is_valid(), "invalid domtree");

        // Skip the entry node and iterate in reverse post-order.
        for &node in postorder.iter().rev().skip(1) {
            assert!(domtree.is_reachable(node), "unreachable node in postorder");

            // Create entries for all reachable nodes.
            self.frontiers.entry(node).or_default();

            let preds = graph
                .preds(node)
                .into_iter()
                .filter(|&pred| domtree.is_reachable(pred));

            // If `a` is in the dominance frontier of `b`, than `b` dominates a predecessor
            // of `a`, but does not strictly dominate `a`.
            for pred in preds {
                let mut runner = pred;
                // The predecessor is not the entry node, so it should have an immediate
                // dominator.
                while runner
                    != domtree
                        .immediate_dominator(node)
                        .expect("non-entry node should have idom")
                {
                    self.frontiers.entry(runner).or_default().push(node);
                    runner = domtree
                        .immediate_dominator(runner)
                        .unwrap_or_else(|| unreachable!());
                }
            }
        }
    }
}

/// An extended dominator tree node with additional information.
///
/// This structure contains dominance frontier information and the top-down
/// structure of the tree, which enables a graph-like traversal on the dominator
/// tree.
///
/// # Type Parameters
///
/// - `N`: The node type of the control flow graph.
struct DomNodeExt<N> {
    // `child` and `sibling` form a linked list for the dominator tree. This structure is derived
    // from Cranelift.
    /// First child node.
    child: Option<N>,
    /// Next sibling node.
    sibling: Option<N>,
    // Pre-order and post-order indices can be used to speed up the query of dominance
    // relationship.
    /// The pre-order index on the dominator tree.
    domtree_preorder: TraversalIdx,
    /// The post-order index on the dominator tree.
    domtree_postorder: TraversalIdx,
    // Depth can be used to find the common ancestor of two nodes.
    /// The depth of the node in the dominator tree.
    domtree_depth: TraversalIdx,
}

impl<N> Default for DomNodeExt<N> {
    fn default() -> Self {
        Self {
            child: None,
            sibling: None,
            domtree_preorder: TraversalIdx::reserved(),
            domtree_postorder: TraversalIdx::reserved(),
            domtree_depth: TraversalIdx::reserved(),
        }
    }
}

/// The iterator over children in the dominator tree.
struct DomTreeChildIter<'a, N> {
    /// The extended dominator tree.
    domtree_ext: &'a DomTreeExt<N>,
    /// Next node to visit.
    next: Option<N>,
}

impl<'a, N> Iterator for DomTreeChildIter<'a, N>
where
    N: Copy + Eq + Hash,
{
    type Item = N;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.next?;
        self.next = self.domtree_ext.extra[&node].sibling;
        Some(node)
    }
}

/// Adapter of dominator trees to compute the dominance frontiers and fast
/// dominance relation query.
pub struct DomTreeExt<N> {
    /// Extra information on nodes.
    extra: HashMap<N, DomNodeExt<N>>,
    /// If the extra information is valid.
    valid: bool,
}

impl<N> Default for DomTreeExt<N> {
    fn default() -> Self {
        Self {
            extra: HashMap::default(),
            valid: false,
        }
    }
}

impl<N> DomTreeExt<N> {
    /// Check if this dominator tree extension is valid.
    pub fn is_valid(&self) -> bool { self.valid }

    /// Invalidate this dominator tree extension.
    pub fn invalidate(&mut self) {
        self.extra.clear();
        self.valid = false;
    }

    /// Query the dominance with the pre-order and post-order in the dominator
    /// tree.
    ///
    /// This method processes the query by comparing the pre-order and
    /// post-order numbers of two nodes in the dominator tree, which is a
    /// O(1) operation.
    ///
    /// # Returns
    ///
    /// - `Some(Dominance)`: If `a` and `b` are in the dominator tree.
    /// - `None`: If `a` or `b` is not in the control flow or not reachable.
    ///
    /// # Panics
    ///
    /// - Panics if this dominator tree extension is invalid.
    pub fn dominance(&self, a: N, b: N) -> Option<Dominance>
    where
        N: Copy + Eq + Hash,
    {
        assert!(self.is_valid(), "invalid domtree extension");

        let pre_a = self.extra.get(&a)?.domtree_preorder;
        let pre_b = self.extra.get(&b)?.domtree_preorder;

        let post_a = self.extra[&a].domtree_postorder;
        let post_b = self.extra[&b].domtree_postorder;

        if a == b {
            return Some(Dominance::Identical);
        }

        if pre_a < pre_b && post_a > post_b {
            return Some(Dominance::Strict);
        }

        Some(Dominance::None)
    }

    /// Query the depth of a node in the dominator tree.
    ///
    /// # Returns
    ///
    /// - `Some(TraversalIdx)`: The depth of the node in the dominator tree.
    /// - `None`: If the node is not in the dominator tree.
    pub fn depth(&self, node: N) -> Option<TraversalIdx>
    where
        N: Copy + Eq + Hash,
    {
        self.extra.get(&node).map(|n| {
            debug_assert_ne!(n.domtree_depth, TraversalIdx::reserved());
            n.domtree_depth
        })
    }

    /// Query the lowest common dominator of two nodes.
    ///
    /// # Parameters
    ///
    /// - `domtree`: The dominator tree.
    /// - `a` & `b`: The nodes to query.
    ///
    /// # Returns
    ///
    /// - `Some(N)`: The common dominator of `a` and `b`.
    /// - `None`: If `a` or `b` is not reachable.
    ///
    /// # Panics
    ///
    /// - Panics if the dominator tree is invalid.
    /// - Panics if the given dominator tree cannot process
    ///   `immediate_dominator` correctly.
    pub fn common_dominator<D>(&self, domtree: &D, a: N, b: N) -> Option<N>
    where
        D: DomTree<Node = N>,
        N: Copy + Eq + Hash,
    {
        assert!(domtree.is_valid(), "invalid domtree");

        if !domtree.is_reachable(a) || !domtree.is_reachable(b) {
            return None;
        }

        let mut a = a;
        let mut b = b;

        while self.depth(a) > self.depth(b) {
            a = domtree
                .immediate_dominator(a)
                .expect("reachable node should have idom");
        }

        while self.depth(b) > self.depth(a) {
            b = domtree
                .immediate_dominator(b)
                .expect("reachable node should have idom");
        }

        while a != b {
            a = domtree
                .immediate_dominator(a)
                .expect("reachable node should have idom");
            b = domtree
                .immediate_dominator(b)
                .expect("reachable node should have idom");
        }

        Some(a)
    }

    /// Compute the dominance extension.
    ///
    /// # Parameters
    ///
    /// - `domtree`: The dominator tree.
    /// - `postorder`: The post-order sequence of the control flow graph.
    ///
    /// # Panics
    ///
    /// - Panics if the dominator tree is invalid.
    /// - Panics if any node in the postorder is unreachable.
    pub fn compute<D>(&mut self, domtree: &D, postorder: &[N])
    where
        D: DomTree<Node = N>,
        N: Copy + Eq + Hash,
    {
        if self.is_valid() {
            return;
        }

        assert!(domtree.is_valid(), "invalid domtree");

        let mut dfs = Dfs::default();

        self.compute_children(domtree, postorder);
        self.prepare_dominance_query(postorder, &mut dfs);
        self.compute_domtree_depth(postorder, &mut dfs);

        self.valid = true;
    }

    fn compute_children<D>(&mut self, domtree: &D, postorder: &[N])
    where
        D: DomTree<Node = N>,
        N: Copy + Eq + Hash,
    {
        for &node in postorder.iter().rev() {
            assert!(domtree.is_reachable(node), "unreachable node in postorder");
            // Create entries for all reachable nodes.
            self.extra.entry(node).or_default();

            let idom = domtree.immediate_dominator(node);
            match idom {
                Some(idom) => {
                    let node_ext = self.extra.entry(idom).or_default();
                    let sibling = mem::replace(&mut node_ext.child, Some(node));
                    self.extra.entry(node).or_default().sibling = sibling;
                }
                None => {
                    // The entry node does not have an immediate dominator.
                }
            }
        }
    }

    fn prepare_dominance_query(&mut self, postorder: &[N], dfs: &mut Dfs<N>)
    where
        N: Copy + Eq + Hash,
    {
        let entry = match postorder.split_last() {
            Some((entry, _)) => *entry,
            None => return, // Empty graph.
        };

        dfs.clear();

        let mut idx = TraversalIdx::zero();
        let domtree_preorder = dfs.preorder_iter_from(self, [entry]).collect::<Vec<_>>();

        for node in domtree_preorder {
            self.extra.get_mut(&node).unwrap().domtree_preorder = idx;
            idx += 1;
        }

        dfs.clear();

        let mut idx = TraversalIdx::zero();
        let domtree_postorder = dfs.postorder_iter_from(self, [entry]).collect::<Vec<_>>();

        for node in domtree_postorder {
            self.extra.get_mut(&node).unwrap().domtree_postorder = idx;
            idx += 1;
        }
    }

    fn compute_domtree_depth(&mut self, postorder: &[N], dfs: &mut Dfs<N>)
    where
        N: Copy + Eq + Hash,
    {
        let entry = match postorder.split_last() {
            Some((entry, _)) => *entry,
            None => return, // Empty graph.
        };

        dfs.clear();

        let domtree_preorder = dfs.preorder_iter_from(self, [entry]).collect::<Vec<_>>();

        self.extra
            .get_mut(&entry)
            .unwrap_or_else(|| unreachable!())
            .domtree_depth = TraversalIdx::zero();

        for node in domtree_preorder.into_iter() {
            let idx = self.extra[&node].domtree_depth + 1;

            let mut child = self.extra[&node].child;
            while let Some(c) = child {
                self.extra
                    .get_mut(&c)
                    .unwrap_or_else(|| unreachable!())
                    .domtree_depth = idx;
                child = self.extra[&c].sibling;
            }
        }
    }
}

impl<N> Graph for DomTreeExt<N>
where
    N: Copy + Eq + Hash,
{
    type Node = N;

    fn is_empty(&self) -> bool { self.extra.is_empty() }
}

impl<N> Succs for DomTreeExt<N>
where
    N: Copy + Eq + Hash,
{
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        DomTreeChildIter {
            domtree_ext: self,
            next: self.extra.get(&node).and_then(|n| n.child),
        }
    }
}
