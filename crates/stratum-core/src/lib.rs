//! # stratum-core
//!
//! The **process grain** of the πρσϕ-Formalism: an implementation of the
//! reflective higher-order (ρ) calculus of Meredith & Radestock,
//! *A Reflective Higher-order Calculus* (ENTCS 141(5), 2005).
//!
//! The ρ-calculus is used here as the *closed* process theory — a calculus in
//! which the theory of names arises wholly from the theory of processes (names
//! are quoted processes) — that will later be reduced to generate traces.
//!
//! ## What this crate provides
//!
//! * [`term`] — the term language ([`Proc`], [`Name`]) and constructors, quote
//!   depth `#(·)`, and free-variable / closedness checks.
//! * [`subst`] — the two substitutions: syntactic (§2.5, α-equivalence, with
//!   impervious quotes) and semantic (§2.7, the reduction engine, where drop
//!   runs code).
//! * [`congruence`] — canonicalization deciding structural congruence `≡`
//!   (§2.3) and name equivalence `≡N` (§2.4).
//! * [`reduce`] — one-step reduction (the `Comm` rule, §2.8) and bounded
//!   reachability, the seed of the trace LTS.
//!
//! Everything above this — the trace LTS, field measurability, and the
//! temporal-logic checker — arrives in later milestones and builds on the
//! canonical forms and reduction defined here.
//!
//! ```
//! use stratum_core::term::{input, output, quote, zero};
//! use stratum_core::congruence::structurally_congruent;
//!
//! // x(y).*y  is α-equivalent to  x(z).*z
//! use stratum_core::term::drop_;
//! let a = input(quote(zero()), |y| drop_(y));
//! let b = input(quote(zero()), |z| drop_(z));
//! assert!(structurally_congruent(&a, &b));
//!
//! // 0 is the unit of parallel composition
//! use stratum_core::term::par;
//! let p = output(quote(zero()), quote(zero()));
//! assert!(structurally_congruent(&par([p.clone(), zero()]), &p));
//! ```

pub mod congruence;
pub mod reduce;
pub mod subst;
pub mod term;

pub use congruence::{canonicalize, canonicalize_name, name_equiv, structurally_congruent};
pub use reduce::{
    is_normal_form, reachable, redexes_with, step, step_labeled, step_labeled_with, step_with,
    Annihilation, NameEquiv, Step, Sync,
};
pub use subst::{subst_semantic, subst_syntactic};
pub use term::{drop_, fresh_sym, input, lift, output, par, quote, zero, Name, Proc};
