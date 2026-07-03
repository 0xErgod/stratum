//! # stratum
//!
//! Umbrella crate for the Stratum toolkit: an executable, verified core for the
//! πρσϕ-Formalism, built on the reflective higher-order (ρ) calculus of Meredith
//! & Radestock. It re-exports each grain as a module so a single `use stratum::…`
//! reaches the whole pipeline — write a protocol in the surface syntax, parse it,
//! build its trace LTS, and check temporal / epistemic / equivalence properties.
//!
//! | Module | Grain | Role |
//! |--------|-------|------|
//! | [`syntax`] | — | parse the `.strat` surface syntax into a [`core::Proc`] |
//! | [`core`]   | π | terms, structural congruence, reduction |
//! | [`lts`]    | ρ | the labelled transition system over reduction |
//! | [`logic`]  | ϕ | modal μ-calculus + epistemic model checking |
//! | [`field`]  | σ | information fields, projections, measurability |
//! | [`equiv`]  | — | N-barbed bisimulation, may-testing |
//!
//! See `crates/stratum/examples/` for worked protocols.

pub use stratum_core as core;
pub use stratum_equiv as equiv;
pub use stratum_field as field;
pub use stratum_logic as logic;
pub use stratum_lts as lts;
pub use stratum_syntax as syntax;
