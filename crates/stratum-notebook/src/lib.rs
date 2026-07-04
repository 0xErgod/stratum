//! # stratum-notebook
//!
//! The reusable, substrate-agnostic notebook core for Stratum. It owns the
//! *interactive* state and presentation logic that any front-end — the Jupyter
//! kernel (`stratum-kernel`), a future web REPL, an LSP server — layers on top
//! of the [`stratum`] toolkit. Keeping this crate free of any transport (no
//! ZeroMQ, no HTTP) is what lets the same evaluation/rendering semantics back
//! every front-end.
//!
//! ## Phase 0 (walking skeleton)
//!
//! This is deliberately a stub. It exposes exactly the two surfaces the Jupyter
//! kernel needs to prove the wire protocol end to end:
//!
//! * [`Namespace`] — the (currently empty) per-session interactive environment.
//!   Later phases grow this into the binding table that accumulates definitions
//!   across cells and feeds completion.
//! * [`render_text`] — the placeholder cell renderer. For now it echoes its
//!   input; later phases turn a parsed [`stratum::core::Proc`] into rich text /
//!   MIME bundles.

#![forbid(unsafe_code)]

/// The per-session interactive environment.
///
/// A [`Namespace`] is the accumulated state of a notebook session: the bindings
/// introduced by earlier cells, cached elaboration results, and (eventually) the
/// handles a front-end needs for completion and inspection. In Phase 0 it carries
/// no state — it exists so the kernel can thread a single owner through its cell
/// handler and so later phases have a stable type to grow into.
#[derive(Debug, Default, Clone)]
pub struct Namespace {
    // Intentionally empty for Phase 0. Future fields (binding table, elaboration
    // cache, source history) land here without changing the front-end contract.
    _private: (),
}

impl Namespace {
    /// Create a fresh, empty namespace for a new notebook session.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
}

/// Render a cell's source into the text that a front-end should display.
///
/// This is the Phase 0 placeholder: it echoes the input verbatim, which is
/// exactly what the kernel walking-skeleton needs to prove that a cell round-trips
/// from front-end to kernel and back. Later phases parse the source with
/// [`stratum::syntax`], evaluate over the [`Namespace`], and return a rich
/// rendering instead of the raw string.
#[must_use]
pub fn render_text(source: &str) -> String {
    source.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn namespace_constructs() {
        let _ns = Namespace::new();
    }

    #[test]
    fn render_text_echoes_input() {
        assert_eq!(render_text("new x in x!(*x)"), "new x in x!(*x)");
        assert_eq!(render_text(""), "");
    }
}
