//! # stratum
//!
//! Umbrella crate for the Stratum toolkit: a verified playground for the
//! reflective higher-order (ρ) calculus of Meredith & Radestock as a protocol
//! design and analysis language. It re-exports each component as a module so a
//! single `use stratum::…` reaches the whole pipeline — write a protocol in the
//! surface syntax, parse it, build its trace LTS, and check temporal / epistemic
//! / equivalence properties.
//!
//! | Module | Role |
//! |--------|------|
//! | [`syntax`] | parse the `.strat` surface syntax into a [`core::Proc`] |
//! | [`core`]   | terms, structural congruence, reduction |
//! | [`lts`]    | the labelled transition system over reduction |
//! | [`logic`]  | modal μ-calculus + epistemic model checking |
//! | [`field`]  | information fields, projections, measurability |
//! | [`types`]  | channel-sort / behavioral typing, a checker over the core |
//! | [`equiv`]  | N-barbed bisimulation, may-testing |
//! | [`encodings`] | derived operators (replication, …) as user-space macros |
//!
//! See `crates/stratum/examples/` for worked protocols.

pub mod encodings;

pub use stratum_core as core;
pub use stratum_equiv as equiv;
pub use stratum_field as field;
pub use stratum_logic as logic;
pub use stratum_lts as lts;
pub use stratum_syntax as syntax;
pub use stratum_types as types;
