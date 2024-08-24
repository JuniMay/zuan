//! Fuzzing Facilities for Graphs.

use alloc::vec::Vec;

use libfuzzer_sys::arbitrary::{self, Unstructured};

use super::{Entry, Preds, Succs};
use crate::core::graph::adapters::TestCFG;
use crate::core::graph::dominance::{DomTree, DomTreeExt, Dominance, DominanceFrontierInfo};
use crate::HashSet;

/// Generate an arbitrary [`TestCFG`] for fuzzing.
pub fn arbitrary_cfg(u: &mut Unstructured) -> arbitrary::Result<TestCFG> {
    let num_nodes = u.int_in_range(0..=4095)?;
    let entry = 0;

    let mut edges = Vec::new();

    for i in 0..num_nodes {
        let num_succs = u.int_in_range(0..=15)?;
        for _ in 0..num_succs {
            let succ = u.int_in_range(0..=(num_nodes - 1))?;
            edges.push((i, succ));
        }
    }

    Ok(TestCFG::new(entry, &edges))
}

/// Generate an arbitrary path on a graph for fuzzing.
pub fn arbitrary_path(u: &mut Unstructured, graph: &TestCFG) -> arbitrary::Result<Vec<usize>> {
    let count = u.int_in_range(0..=(2 * graph.num_nodes()))?;
    let entry = graph.entry().unwrap();

    let mut path = vec![entry];
    let mut node = entry;

    for _ in 0..count {
        let succs = graph.succs(node).into_iter().collect::<Vec<_>>();
        if succs.is_empty() {
            break;
        }
        node = *u.choose(&succs)?;
        path.push(node);
    }

    Ok(path)
}

/// Check if there are any violations of dominance in the dominator tree.
pub fn check_domtree<D>(graph: &TestCFG, path: &[usize], domtree: &mut D)
where
    D: DomTree<Node = usize>,
{
    assert!(!domtree.is_valid());

    domtree.compute(graph);
    assert!(domtree.is_valid());

    let mut visited = HashSet::new();

    for &node in path {
        assert!(domtree.is_reachable(node));

        let mut dominators = HashSet::new();
        dominators.insert(node);

        let mut idom = domtree.immediate_dominator(node);
        while let Some(d) = idom {
            assert!(visited.contains(&d));
            assert!(!dominators.contains(&d));
            dominators.insert(d);
            idom = domtree.immediate_dominator(d);
        }

        for maybe_dominator in 0..graph.num_nodes() {
            assert_eq!(
                dominators.contains(&maybe_dominator),
                domtree
                    .dominance(maybe_dominator, node)
                    // Testing the correctness of boolean conversion
                    .map(bool::from)
                    .unwrap_or(false)
            );
            // More detailed check
            if maybe_dominator == node {
                assert!(dominators.contains(&maybe_dominator));
                assert!(domtree.is_reachable(maybe_dominator));
                assert_eq!(
                    domtree.dominance(maybe_dominator, node),
                    Some(Dominance::Identical)
                );
            } else if dominators.contains(&maybe_dominator) {
                assert!(domtree.is_reachable(maybe_dominator));
                assert_eq!(
                    domtree.dominance(maybe_dominator, node),
                    Some(Dominance::Strict)
                );
            } else if domtree.is_reachable(maybe_dominator) {
                assert_eq!(
                    domtree.dominance(maybe_dominator, node),
                    Some(Dominance::None)
                );
            } else {
                assert_eq!(domtree.dominance(maybe_dominator, node), None);
            }
        }

        visited.insert(node);
    }
}

/// Check the extended dominator tree and the dominance frontier.
pub fn check_domtree_ext<D>(graph: &TestCFG, domtree: &D, postorder: &[usize])
where
    D: DomTree<Node = usize>,
{
    let mut domtree_ext = DomTreeExt::default();
    let mut df = DominanceFrontierInfo::default();
    domtree_ext.compute(domtree, postorder);
    df.compute(graph, domtree, postorder);

    for &node in postorder {
        // Check the dominance frontier by definition.
        for &frontier_node in df.frontier(node) {
            assert_ne!(
                domtree_ext.dominance(node, frontier_node).unwrap(),
                Dominance::Strict
            );
            let mut dom_pred = false;
            for pred in graph.preds(frontier_node) {
                match domtree_ext.dominance(node, pred) {
                    Some(Dominance::None) => {}
                    Some(Dominance::Identical | Dominance::Strict) => {
                        dom_pred = true;
                        break;
                    }
                    None => assert!(!domtree.is_reachable(pred)),
                }
            }
            assert!(dom_pred);
        }

        // Check the child iterator on the domtree
        for child in domtree_ext.succs(node) {
            assert_eq!(domtree.immediate_dominator(child), Some(node));
            let node_depth = domtree_ext.depth(node).unwrap();
            let child_depth = domtree_ext.depth(child).unwrap();
            assert!(node_depth < child_depth);
        }
    }
}
