//! Build script.
//!
//! Under the default feature set this is a no-op — the crate is pure Rust. Only
//! when the off-by-default `tree-sitter` feature is enabled do we compile the
//! generated C parser, which is the sole place a C toolchain is required.

fn main() {
    #[cfg(feature = "tree-sitter")]
    {
        let src_dir = std::path::Path::new("tree-sitter/src");
        let parser = src_dir.join("parser.c");
        println!("cargo:rerun-if-changed={}", parser.display());
        cc::Build::new()
            .include(src_dir)
            .file(&parser)
            .warnings(false)
            .compile("tree-sitter-stratum");
    }
}
