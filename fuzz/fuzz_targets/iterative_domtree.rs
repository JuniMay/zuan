#![no_main]

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::{arbitrary, fuzz_target};
use zuan::core::graph::adapters::TestCFG;
use zuan::core::graph::dominance::IterativeDomTree;
use zuan::core::graph::fuzzing::{arbitrary_cfg, arbitrary_path, check_domtree};

#[derive(Debug)]
struct TestCase {
    graph: TestCFG,
    path: Vec<usize>,
}

impl Arbitrary<'_> for TestCase {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let graph = arbitrary_cfg(u)?;
        let path = arbitrary_path(u, &graph)?;
        Ok(TestCase { graph, path })
    }
}

fuzz_target!(|testcase: TestCase| {
    let mut domtree = IterativeDomTree::default();
    check_domtree(&testcase.graph, &testcase.path, &mut domtree);
});
