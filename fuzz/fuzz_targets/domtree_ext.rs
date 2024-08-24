#![no_main]

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::{arbitrary, fuzz_target};
use zuan::core::graph::adapters::TestCFG;
use zuan::core::graph::dominance::{DomTree, IterativeDomTree};
use zuan::core::graph::fuzzing::{arbitrary_cfg, check_domtree_ext};

#[derive(Debug)]
struct TestCase {
    graph: TestCFG,
}

impl Arbitrary<'_> for TestCase {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let graph = arbitrary_cfg(u)?;
        Ok(TestCase { graph })
    }
}

fuzz_target!(|testcase: TestCase| {
    let mut domtree = IterativeDomTree::default();
    domtree.compute(&testcase.graph);
    check_domtree_ext(&testcase.graph, &domtree, domtree.postorder());
});
