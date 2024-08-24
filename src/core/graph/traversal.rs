//! Utilities for Graph Traversal

use alloc::vec::Vec;
use core::hash::Hash;
use core::ops;

use crate::core::graph::{Entry, Graph, Succs};
use crate::core::utils::{Idx, Reserved};
use crate::HashSet;

/// An event in a graph traversal.
#[derive(Debug, Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum DfsEvent {
    /// Entering a node.
    Enter,
    /// Leaving a node.
    Leave,
}

/// A depth-first search state.
///
/// # Type Parameters
///
/// - `N`: The type of nodes in the graph.
pub struct Dfs<N> {
    /// The stack of depth-first search events.
    stack: Vec<(DfsEvent, N)>,
    /// The set of visited nodes.
    visited: HashSet<N>,
}

impl<N> Default for Dfs<N> {
    fn default() -> Self {
        Self {
            stack: Vec::new(),
            visited: HashSet::new(),
        }
    }
}

impl<N> Dfs<N> {
    /// Clear the state.
    pub fn clear(&mut self) {
        self.stack.clear();
        self.visited.clear();
    }

    /// Start a depth-first search on the graph.
    ///
    /// For dedicated pre-order or post-order traversing, check
    /// [`preorder_iter`](Self::preorder_iter) and
    /// [`postorder_iter`](Self::postorder_iter).
    ///
    /// # Returns
    ///
    /// A [`DfsIter`] that yields events, visiting information and nodes.
    pub fn iter<'a, G>(&'a mut self, graph: &'a G) -> DfsIter<'a, G>
    where
        G: Graph<Node = N> + Succs + Entry,
    {
        self.iter_from(graph, graph.entry())
    }

    /// Start a depth-first search on the graph and yield nodes in a pre-order.
    ///
    /// # Returns
    ///
    /// A [`DfsPreorderIter`] that yields nodes in a pre-order.
    pub fn preorder_iter<'a, G>(&'a mut self, graph: &'a G) -> DfsPreorderIter<'a, G>
    where
        G: Graph<Node = N> + Succs + Entry,
    {
        DfsPreorderIter(self.iter(graph))
    }

    /// Start a depth-first search on the graph and yield nodes in a post-order.
    ///
    /// # Returns
    ///
    /// A [`DfsPostorderIter`] that yields nodes in a post-order.
    pub fn postorder_iter<'a, G>(&'a mut self, graph: &'a G) -> DfsPostorderIter<'a, G>
    where
        G: Graph<Node = N> + Succs + Entry,
    {
        DfsPostorderIter(self.iter(graph))
    }

    /// Start a depth-first search from certain nodes on the graph.
    ///
    /// # Returns
    ///
    /// A [`DfsIter`] that yields events, with given nodes as the starting
    /// points.
    pub fn iter_from<'a, G>(
        &'a mut self,
        graph: &'a G,
        nodes: impl IntoIterator<Item = N>,
    ) -> DfsIter<'a, G>
    where
        G: Graph<Node = N> + Succs,
    {
        self.clear();
        self.stack
            .extend(nodes.into_iter().map(|node| (DfsEvent::Enter, node)));
        DfsIter { graph, state: self }
    }

    /// Start a depth-first search from certain nodes on the graph and yield
    /// nodes in a pre-order.
    ///
    /// # Returns
    ///
    /// A [`DfsPreorderIter`] that yields nodes in a pre-order, with given nodes
    /// as the starting points.
    pub fn preorder_iter_from<'a, G>(
        &'a mut self,
        graph: &'a G,
        nodes: impl IntoIterator<Item = N>,
    ) -> DfsPreorderIter<'a, G>
    where
        G: Graph<Node = N> + Succs,
    {
        DfsPreorderIter(self.iter_from(graph, nodes))
    }

    /// Start a depth-first search from certain nodes on the graph and yield
    /// nodes in a post-order.
    ///
    /// # Returns
    ///
    /// A [`DfsPostorderIter`] that yields nodes in a post-order, with given
    /// nodes as the starting points.
    pub fn postorder_iter_from<'a, G>(
        &'a mut self,
        graph: &'a G,
        nodes: impl IntoIterator<Item = N>,
    ) -> DfsPostorderIter<'a, G>
    where
        G: Graph<Node = N> + Succs,
    {
        DfsPostorderIter(self.iter_from(graph, nodes))
    }
}

/// An iterator for depth-first search.
///
/// The item yielded by the iterator is a tuple of `(event, node, first_visit)`.
/// The `event` is the event of the depth-first search, `node` is the node being
/// visited, and `first_visit` indicates whether the node is visited for the
/// first time.
///
/// - `Enter` & `true`: The node is visited for the first time.
/// - `Enter` & `false`: The node is visited before but entered again.
/// - `Leave` & `false`: All the children of the node are visited.
pub struct DfsIter<'a, G: Graph> {
    /// The graph being traversed.
    graph: &'a G,
    /// The depth-first search state.
    state: &'a mut Dfs<G::Node>,
}

impl<'a, G> Iterator for DfsIter<'a, G>
where
    G: Graph + Succs,
{
    type Item = (DfsEvent, G::Node, bool);

    fn next(&mut self) -> Option<Self::Item> {
        let (event, node) = self.state.stack.pop()?;

        match event {
            DfsEvent::Enter => {
                if self.state.visited.insert(node) {
                    // This is a tree edge.
                    self.state.stack.push((DfsEvent::Leave, node));
                    self.state.stack.extend(
                        self.graph
                            .succs(node)
                            .into_iter()
                            .map(|succ| (DfsEvent::Enter, succ)),
                    );
                    Some((DfsEvent::Enter, node, true))
                } else {
                    // This is a forward, cross or back-edge. We do not record if a node is
                    // blackened, so we cannot distinguish back-edges here. However, additional
                    // space can be attached to check the kinds of edges.
                    Some((DfsEvent::Enter, node, false))
                }
            }
            // `Leave` event cannot be the second time we visit a node.
            DfsEvent::Leave => Some((DfsEvent::Leave, node, false)),
        }
    }
}

/// Detect if the graph is cyclic.
///
/// This is based on the depth-first search techniques described in
/// *Introduction to Algorithms*, which utilizes the white-grey-black coloring
/// scheme. In [`DfsIter`], we have already provided the interface to check if a
/// node is visited before and the kinds of event when visiting a node. If we
/// enter a node that is already visited but not settled (blackened), then we
/// have detected a back-edge, which indicates a cycle in the graph.
///
/// The `visited` set in [`Dfs`] together with the [`DfsEvent`] already
/// indicates if a node is greyed before, all we need to do is to attach a
/// `settled` set for blackened nodes. This is also the way rustc implements the
/// `TriColorDepthFirstSearch` in `rustc_data_structures`.
pub fn is_cyclic<G>(graph: &G) -> bool
where
    G: Graph + Succs + Entry,
{
    let mut settled = HashSet::new();
    let mut dfs = Dfs::default();
    for (event, node, first_visit) in dfs.iter(graph) {
        match event {
            DfsEvent::Enter if !first_visit && !settled.contains(&node) => {
                // The node is visited before but not settled (blackened), so this is a grey
                // node and a back-edge.
                return true;
            }
            DfsEvent::Enter => {
                // The node is visited for the first time, or already settled,
                // no back-edge detected.
            }
            DfsEvent::Leave => {
                // All the children of the node are visited, so we can blacken the node.
                settled.insert(node);
            }
        }
    }
    false
}

/// A depth-first search iterator that yields nodes in a pre-order.
pub struct DfsPreorderIter<'a, G: Graph>(DfsIter<'a, G>);

impl<'a, G> Iterator for DfsPreorderIter<'a, G>
where
    G: Graph + Succs,
{
    type Item = G::Node;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                (DfsEvent::Enter, node, true) => return Some(node),
                _ => continue,
            }
        }
    }
}

/// A depth-first search iterator that yields nodes in a post-order.
pub struct DfsPostorderIter<'a, G: Graph>(DfsIter<'a, G>);

impl<'a, G> Iterator for DfsPostorderIter<'a, G>
where
    G: Graph + Succs,
{
    type Item = G::Node;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.next()? {
                (DfsEvent::Leave, node, _) => return Some(node),
                _ => continue,
            }
        }
    }
}

/// An index for a node in a depth-first search.
///
/// This can be used to represent a pre-order, post-order or reverse post-order
/// number. The index can be initialized as zero, then incremented by `+` or
/// `+=` with [`usize`] numbers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TraversalIdx(usize);

impl Idx for TraversalIdx {
    fn index(self) -> usize { self.0 }
}

impl Reserved for TraversalIdx {
    fn reserved() -> Self { Self(usize::MAX) }

    fn is_reserved(&self) -> bool { self.0 == usize::MAX }
}

impl TraversalIdx {
    /// Create a new zero index.
    pub fn zero() -> Self { Self(0) }
}

impl ops::Add<usize> for TraversalIdx {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output { Self(self.0 + rhs) }
}

impl ops::AddAssign<usize> for TraversalIdx {
    fn add_assign(&mut self, rhs: usize) { self.0 += rhs; }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::graph::adapters::TestCFG;

    #[test]
    fn test_cyclic() {
        use crate::core::graph::traversal::is_cyclic;

        let acyclic = TestCFG::new(0, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        let cyclic = TestCFG::new(0, &[(0, 1), (1, 2), (2, 3), (3, 0)]);

        assert!(!is_cyclic(&acyclic));
        assert!(is_cyclic(&cyclic));
    }

    #[test]
    fn test_dfs() {
        use DfsEvent::{Enter, Leave};

        use crate::core::graph::traversal::{Dfs, DfsEvent};

        let graph = TestCFG::new(0, &[(0, 1), (1, 2), (1, 3), (2, 3)]);

        let mut dfs = Dfs::default();
        let mut iter = dfs.iter(&graph);

        assert_eq!(iter.next(), Some((Enter, 0, true)));
        assert_eq!(iter.next(), Some((Enter, 1, true)));
        assert_eq!(iter.next(), Some((Enter, 3, true)));
        assert_eq!(iter.next(), Some((Leave, 3, false)));
        assert_eq!(iter.next(), Some((Enter, 2, true)));
        assert_eq!(iter.next(), Some((Enter, 3, false)));
        assert_eq!(iter.next(), Some((Leave, 2, false)));
        assert_eq!(iter.next(), Some((Leave, 1, false)));
        assert_eq!(iter.next(), Some((Leave, 0, false)));
    }

    #[test]
    fn test_preorder() {
        use crate::core::graph::traversal::Dfs;

        let graph = TestCFG::new(0, &[(0, 1), (1, 2), (1, 3), (2, 3)]);

        let mut dfs = Dfs::default();
        let mut iter = dfs.preorder_iter(&graph);

        let result: Vec<_> = iter.by_ref().collect();
        assert_eq!(result, vec![0, 1, 3, 2]);
    }

    #[test]
    fn test_postorder() {
        use crate::core::graph::traversal::Dfs;

        let graph = TestCFG::new(0, &[(0, 1), (1, 2), (1, 3), (2, 3)]);

        let mut dfs = Dfs::default();
        let mut iter = dfs.postorder_iter(&graph);

        let result: Vec<_> = iter.by_ref().collect();
        assert_eq!(result, vec![3, 2, 1, 0]);
    }
}
