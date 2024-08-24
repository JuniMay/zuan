//! Control Flow Information

use alloc::vec::Vec;
use core::hash::Hash;

use crate::core::graph::{ControlFlowGraph, Entry, Graph, Preds, Succs};
use crate::{HashMap, HashSet};

/// Control flow graph information derived from a graph.
///
/// This is useful when a graph needs to be modified but the original control
/// flow information is still needed, or the graph does not implement [`Preds`].
#[derive(Debug, Clone)]
pub struct ControlFlowInfo<N> {
    /// The entry node, [`None`] if the graph is empty.
    entry: Option<N>,
    /// The successor information
    succs: HashMap<N, Vec<N>>,
    /// The predecessor information
    preds: HashMap<N, Vec<N>>,
    /// If the predecessors are valid.
    valid: bool,
}

impl<N> Default for ControlFlowInfo<N> {
    fn default() -> Self {
        Self {
            entry: None,
            succs: HashMap::new(),
            preds: HashMap::new(),
            valid: false,
        }
    }
}

impl<N> ControlFlowInfo<N> {
    /// Check if the control flow information is valid.
    pub fn is_valid(&self) -> bool { self.valid }

    /// Clear and invalidate the control flow information.
    pub fn invalidate(&mut self) {
        self.entry = None;
        self.succs.clear();
        self.preds.clear();
        self.valid = false;
    }

    /// Compute the control flow information from a graph.
    ///
    /// Only the reachable nodes will be included in the control flow
    /// information.
    pub fn compute<G>(&mut self, graph: &G)
    where
        G: Graph<Node = N> + Entry + Succs,
        N: Copy + Eq + Hash,
    {
        let mut worklist = Vec::new();
        let mut visited = HashSet::new();

        if !graph.is_empty() {
            self.entry = graph.entry();
            worklist.extend(self.entry);
        }

        while let Some(node) = worklist.pop() {
            if !visited.insert(node) {
                continue;
            }

            self.succs.entry(node).or_default();
            self.preds.entry(node).or_default();

            for succ in graph.succs(node) {
                self.succs.entry(node).or_default().push(succ);
                self.preds.entry(succ).or_default().push(node);
                worklist.push(succ);
            }
        }

        self.valid = true;
    }

    /// Get the number of nodes in the graph.
    ///
    /// If this graph is derived from a control flow graph, this should be the
    /// number of reachable nodes.
    pub fn num_nodes(&self) -> usize {
        debug_assert_eq!(self.succs.len(), self.preds.len());
        self.succs.len()
    }
}

impl ControlFlowInfo<usize> {
    /// Create a new graph with given entry node and edges.
    ///
    /// This is typically used for testing.
    pub fn new(entry: usize, edges: &[(usize, usize)]) -> Self {
        let mut succs = HashMap::new();
        let mut preds = HashMap::new();
        let mut num_nodes = entry + 1;

        for &(src, dst) in edges {
            succs.entry(src).or_insert_with(Vec::new).push(dst);
            preds.entry(dst).or_insert_with(Vec::new).push(src);
            num_nodes = num_nodes.max(src + 1).max(dst + 1);
        }

        for i in 0..num_nodes {
            succs.entry(i).or_default();
            preds.entry(i).or_default();
        }

        Self {
            entry: Some(entry),
            succs,
            preds,
            valid: true,
        }
    }

    /// Create an empty graph for testing.
    pub fn empty() -> Self {
        Self {
            entry: None,
            succs: HashMap::new(),
            preds: HashMap::new(),
            valid: true,
        }
    }
}

/// Alias of [`ControlFlowInfo`] for testing.
pub type TestCFG = ControlFlowInfo<usize>;

impl<N> Graph for ControlFlowInfo<N>
where
    N: Copy + Eq + Hash,
{
    type Node = N;

    fn is_empty(&self) -> bool { self.entry.is_none() }
}

impl<N> Entry for ControlFlowInfo<N>
where
    N: Copy + Eq + Hash,
{
    fn entry(&self) -> Option<Self::Node> { self.entry }
}

impl<N> Succs for ControlFlowInfo<N>
where
    N: Copy + Eq + Hash,
{
    fn succs(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        self.succs
            .get(&node)
            .into_iter()
            .flat_map(|v| v.iter().copied())
    }
}

impl<N> Preds for ControlFlowInfo<N>
where
    N: Copy + Eq + Hash,
{
    fn preds(&self, node: Self::Node) -> impl IntoIterator<Item = Self::Node> {
        self.preds
            .get(&node)
            .into_iter()
            .flat_map(|v| v.iter().copied())
    }
}

impl<N> ControlFlowGraph for ControlFlowInfo<N> where N: Copy + Eq + Hash {}
