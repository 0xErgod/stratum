//! # stratum-logic
//!
//! The **temporal-logic grain** (ϕ) of the πρσϕ-Formalism: a modal μ-calculus
//! model checker over the ρ-calculus trace LTS ([`stratum_lts`]).
//!
//! The μ-calculus is chosen for *full temporal expressiveness* — it subsumes
//! LTL and CTL — so safety, liveness, and richer branching-time properties are
//! all expressible. Atomic propositions are decided per state by a caller-
//! supplied labelling `Fn(&str, &Proc) -> bool`; the checker computes the set of
//! states satisfying a formula by fixpoint iteration, and can extract witness /
//! counterexample runs.
//!
//! ```
//! use stratum_core::term::{input, lift, quote, zero, par};
//! use stratum_lts::Lts;
//! use stratum_logic::{check::holds, formula::{ag, ef, prop}};
//!
//! // a⟨|0|⟩ | a(y).done⟨|0|⟩ : after one Comm the system emits on `done`.
//! let a = quote(zero());
//! let done = quote(lift(quote(zero()), zero()));
//! let sys = par([lift(a.clone(), zero()), input(a, {
//!     let d = done.clone();
//!     move |_| lift(d.clone(), zero())
//! })]);
//! let lts = Lts::explore(&sys, 100);
//!
//! // "done" holds where a top-level lift on channel `done` is present.
//! let d = done.clone();
//! let label = |p: &str, proc: &stratum_core::Proc| match p {
//!     "done" => stratum_logic::examples::emits(proc, &d),
//!     _ => false,
//! };
//!
//! assert!(holds(&lts, &ef(prop("done")), &label));   // reachable
//! assert!(!holds(&lts, &ag(prop("done")), &label));  // not invariant
//! ```

pub mod check;
pub mod formula;

pub use check::{
    check, check_epistemic, check_fair, counterexample, holds, holds_checked, holds_epistemic,
    holds_fair, satisfies, satisfies_checked, shortest_path, witness, Agents, Checked, Fairness,
};
pub use formula::{
    af, ag, and, boxm, can, diamond, ef, eg, ex, fair_af, fair_eg, ff, knows, mu, neg, nu, or,
    possible, prop, tt, var, Action, Formula,
};

/// Small state predicates handy for atomic propositions in examples and tests.
pub mod examples {
    use stratum_core::{name_equiv, Name, Proc};

    /// The active parallel components of a (canonical) process.
    fn components(p: &Proc) -> Vec<&Proc> {
        match p {
            Proc::Zero => Vec::new(),
            Proc::Par(ps) => ps.iter().collect(),
            other => vec![other],
        }
    }

    /// Whether `p` has a top-level lift (output) on a channel `≡N channel`.
    pub fn emits(p: &Proc, channel: &Name) -> bool {
        components(p).into_iter().any(|c| match c {
            Proc::Lift { chan, .. } => name_equiv(chan, channel),
            _ => false,
        })
    }
}
