//! Smoke test for the optional tree-sitter binding.
//!
//! Only compiled/run under the off-by-default `tree-sitter` feature:
//! `cargo test -p stratum-syntax --features tree-sitter`.

#![cfg(feature = "tree-sitter")]

use tree_sitter::Parser;

#[test]
fn loads_language_and_parses() {
    let mut parser = Parser::new();
    parser
        .set_language(&stratum_syntax::tree_sitter_language())
        .expect("load stratum grammar");

    let tree = parser.parse("@0!(0) | @0(y).*y", None).unwrap();
    let root = tree.root_node();
    assert_eq!(root.kind(), "source_file");
    assert!(!root.has_error());
    // Top-level construct is a parallel composition.
    assert_eq!(root.child(0).unwrap().kind(), "parallel");
}
