//! Iterative Algorithm for Dominator Tree Construction.

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::hash::Hash;

use super::{DomTree, Dominance};
use crate::core::graph::traversal::{Dfs, TraversalIdx};
use crate::core::graph::ControlFlowGraph;
use crate::HashMap;

/// A node in the iterative dominator tree.
struct IterativeDomNode<N> {
    // rpo index is assigned every time the node is created, it is not optional.
    /// The reverse post-order index of this node in the control flow graph.
    rpo: TraversalIdx,
    /// The immediate dominator of this node.
    idom: Option<N>,
}

impl<N> IterativeDomNode<N> {
    fn new(rpo: TraversalIdx, idom: Option<N>) -> Self { Self { rpo, idom } }
}

/// An iterative dominator tree.
///
/// This dominator tree type implements the algorithm described in *A Simple,
/// Fast Dominance Algorithm* by Cooper, Harvey, and Kennedy. The algorithm is
/// iterative and not intended to be maintained dynamically.
///
/// # Type Parameters
///
/// `N`: The type of the node in the control flow graph.
pub struct IterativeDomTree<N> {
    /// All the reachable nodes in the dominator tree.
    nodes: HashMap<N, IterativeDomNode<N>>,
    /// The post-order sequence in the control flow graph.
    postorder: Vec<N>,
    /// The depth-first search state.
    ///
    /// The state can be reused when re-computation is needed.
    dfs: Dfs<N>,
    /// If this dominator tree is valid.
    valid: bool,
}

impl<N> DomTree for IterativeDomTree<N>
where
    N: Copy + Eq + Hash,
{
    type Node = N;

    fn compute<G>(&mut self, graph: &G)
    where
        G: ControlFlowGraph<Node = N>,
    {
        if self.is_valid() {
            return;
        }
        self.compute_postorder(graph);
        self.compute_domtree(graph);
        self.valid = true;
    }

    fn is_valid(&self) -> bool { self.valid }

    fn invalidate(&mut self) {
        self.nodes.clear();
        self.postorder.clear();
        self.valid = false;
    }

    fn is_reachable(&self, node: N) -> bool { self.nodes.contains_key(&node) }

    fn immediate_dominator(&self, node: N) -> Option<N> {
        self.nodes.get(&node).and_then(|n| n.idom)
    }

    fn dominance(&self, a: N, b: N) -> Option<Dominance> {
        if !self.is_reachable(a) || !self.is_reachable(b) {
            return None;
        }

        if a == b {
            return Some(Dominance::Identical);
        }

        let mut idom = self.immediate_dominator(b);

        while let Some(d) = idom {
            if d == a {
                return Some(Dominance::Strict);
            }
            idom = self.immediate_dominator(d);
        }
        Some(Dominance::None)
    }
}

impl<N> Default for IterativeDomTree<N> {
    fn default() -> Self {
        Self {
            nodes: HashMap::new(),
            postorder: Vec::new(),
            dfs: Dfs::default(),
            valid: false,
        }
    }
}

impl<N> IterativeDomTree<N>
where
    N: Copy + Eq + Hash,
{
    fn compute_postorder<G>(&mut self, graph: &G)
    where
        G: ControlFlowGraph<Node = N>,
    {
        debug_assert!(self.postorder.is_empty());
        self.postorder.extend(self.dfs.postorder_iter(graph))
    }

    fn compute_domtree<G>(&mut self, graph: &G)
    where
        G: ControlFlowGraph<Node = N>,
    {
        debug_assert!(!self.is_valid());

        let (entry, postorder) = match self.postorder.as_slice().split_last() {
            Some((entry, postorder)) => (*entry, postorder),
            None => return, // Empty graph.
        };

        // There should be an entry for non-empty graph.
        debug_assert!(entry == graph.entry().unwrap());

        // Initial reverse post-order index is zero (which is not the reserved value)
        let mut counter = TraversalIdx::zero();

        // Cranelift reserved `0` for unreachable nodes, but as we only store reachable
        // nodes in the domtree, this is not necessary.
        self.nodes
            .insert(entry, IterativeDomNode::new(counter, None));

        // Iterate all reachable nodes in the postorder sequence except the entry node.
        for &node in postorder.iter().rev() {
            counter += 1;
            let idom = self.compute_idom(graph, node);
            self.nodes
                .insert(node, IterativeDomNode::new(counter, Some(idom)));
        }

        // Iterate until the dominator tree is stable.
        let mut changed = true;
        while changed {
            changed = false;
            for &node in postorder.iter().rev() {
                let idom = self.compute_idom(graph, node);
                let node = self.nodes.get_mut(&node).unwrap_or_else(|| unreachable!());
                if node.idom != Some(idom) {
                    node.idom = Some(idom);
                    changed = true;
                }
            }
        }
    }

    fn compute_idom<G>(&self, graph: &G, node: N) -> N
    where
        G: ControlFlowGraph<Node = N>,
    {
        let mut reachable_preds = graph
            .preds(node)
            .into_iter()
            // Filter out unreachable (not computed yet) predecessors, because we cannot compute the
            // common dominators with them.
            .filter(|n| self.is_reachable(*n));

        // We called `compute_idom` in `compute_domtree` when traversing the nodes in
        // reverse post-order, so at least one predecessor should have been computed in
        // the domtree.
        let mut idom = reachable_preds
            .next()
            .expect("node should have at least one reachable predecessor");

        for pred in reachable_preds {
            idom = self.intersect(idom, pred);
        }
        idom
    }

    /// Query the rpo index relationship between two nodes.
    ///
    /// If `a` is *smaller* than `b` in rpo number, it means that `a` appears
    /// *earlier* in the control flow graph when traversing in reverse
    /// post-order.
    ///
    /// Note that not all algorithms for dominator tree construction require a
    /// reverse post-order sequence. This method is typically used in
    /// `intersect` for computing the common dominator.
    ///
    /// # Returns
    ///
    /// - `Some(Ordering)`: The relationship between the two nodes.
    /// - `None`: Either of the nodes is unreachable or does not exist.
    pub fn rpo_cmp(&self, a: N, b: N) -> Option<Ordering> {
        let a_rpo = self.nodes.get(&a)?.rpo;
        let b_rpo = self.nodes.get(&b)?.rpo;
        Some(a_rpo.cmp(&b_rpo))
    }

    /// Get all nodes in post-order.
    ///
    /// # See also
    ///
    /// - [`rpo_cmp`](Self::rpo_cmp): Compare two nodes in reverse post-order.
    pub fn postorder(&self) -> &[N] { &self.postorder }

    /// Compute the common dominator of two nodes.
    ///
    /// If either of the nodes is unreachable, or not computed in the dominator
    /// tree, this function returns `None`.
    ///
    /// # Panics
    ///
    /// Panics if the nodes are not reachable or do not exist. This function
    /// should not panic when computing in reverse post-order.
    fn intersect(&self, a: N, b: N) -> N {
        let mut finger1 = a;
        let mut finger2 = b;

        while finger1 != finger2 {
            while let Ordering::Less = self.rpo_cmp(finger1, finger2).expect("rpo should exist") {
                finger2 = self
                    .immediate_dominator(finger2)
                    .expect("idom should exist for non-entry reachable node");
            }
            while let Ordering::Less = self.rpo_cmp(finger2, finger1).expect("rpo should exist") {
                finger1 = self
                    .immediate_dominator(finger1)
                    .expect("idom should exist for non-entry reachable node");
            }
        }

        finger1
    }
}
