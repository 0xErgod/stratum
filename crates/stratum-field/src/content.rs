//! Payload-granularity coordinate content (SPEC §F3).
//!
//! The static field core takes `content(c)` to be **presence**: does the state
//! have a top-level output (barb) on channel `c`? (see [`crate::project`]). §F3
//! promises a finer choice — the **payload multiset**: *what* is pending on `c`,
//! not merely *whether* something is. This module delivers it while leaving the
//! presence API ([`crate::project`], [`crate::observational_field`]) untouched
//! and the agent model (§F5) unchanged; payload is simply a richer `content(c)`.
//!
//! For an observed channel `c`, the payload coordinate is the multiset of
//! canonical lifted processes carried by the top-level lifts on `c`: each
//! top-level `Lift { chan, arg }` with `chan ≡N c` contributes `canonicalize(arg)`.
//! Payload is at least as fine as presence — the presence coordinate is exactly
//! "is the payload multiset non-empty?" — so [`payload_field`] always refines
//! [`crate::observational_field`] (§F7).
//!
//! ```
//! use stratum_core::term::{input, lift, quote, zero, par};
//! use stratum_lts::Lts;
//! use stratum_field::{observational_field};
//! use stratum_field::content::payload_field;
//!
//! // Two runs both emit on c, but with different payloads.
//! let c = quote(zero());
//! let a = quote(lift(quote(zero()), zero()));
//! let sys = par([
//!     lift(a.clone(), zero()),
//!     input(a.clone(), { let c = c.clone(); move |_| lift(c, zero()) }),
//!     input(a, { let c = c.clone(); move |_| lift(c, lift(quote(zero()), zero())) }),
//! ]);
//! let lts = Lts::explore(&sys, 100);
//! // Payload separates the two emitters that presence lumps together.
//! assert!(payload_field(&lts, &[c.clone()]).refines(&observational_field(&lts, &[c])));
//! ```

use std::collections::BTreeMap;
use std::hash::Hash;

use stratum_core::{canonicalize, canonicalize_name, name_equiv, Name, Proc};
use stratum_lts::Lts;

use crate::Field;

/// Active parallel components of a (canonical) process — its top-level
/// sub-processes, treating `0` as empty and a non-parallel term as a singleton.
fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Zero => Vec::new(),
        Proc::Par(ps) => ps.iter().collect(),
        other => vec![other],
    }
}

/// The **payload projection** of a state onto observed channels (§F3): for each
/// observed channel, the multiset of canonical payload processes pending on it.
///
/// For every observed channel `c` (returned as its canonical name) that carries
/// at least one top-level output, the value is a `payload → count` multiset: each
/// top-level `Lift { chan, arg }` with `chan ≡N c` contributes `canonicalize(arg)`.
/// Channels with no top-level output are omitted, so the key set of the result is
/// exactly the presence projection [`crate::project`] — payload strictly extends
/// presence with the *contents* of each barb.
pub fn project_payload(state: &Proc, obs: &[Name]) -> BTreeMap<Name, BTreeMap<Proc, usize>> {
    let comps = components(state);
    let mut out: BTreeMap<Name, BTreeMap<Proc, usize>> = BTreeMap::new();
    for c in obs {
        let mut multiset: BTreeMap<Proc, usize> = BTreeMap::new();
        for k in &comps {
            if let Proc::Lift { chan, arg } = k {
                if name_equiv(chan, c) {
                    *multiset.entry(canonicalize(arg)).or_insert(0) += 1;
                }
            }
        }
        if !multiset.is_empty() {
            out.insert(canonicalize_name(c), multiset);
        }
    }
    out
}

/// Generic observational field (§F6): partition the LTS states by the value of a
/// projection `project_fn`, two states sharing an atom iff their projections are
/// equal.
///
/// This is the shared engine behind both the presence field
/// ([`crate::observational_field`]) and the payload field ([`payload_field`]):
/// they differ only in the coordinate content `S` (§F3) they project onto.
pub fn observational_field_by<S: Eq + Hash + Clone>(
    lts: &Lts,
    project_fn: impl Fn(&Proc) -> S,
) -> Field {
    let signatures: Vec<S> = (0..lts.num_states())
        .map(|i| project_fn(lts.state(i)))
        .collect();
    Field::from_signatures(&signatures)
}

/// The **payload field** over the LTS induced by observing `obs` (§F3): states
/// are in the same atom iff their payload projections ([`project_payload`]) are
/// equal.
///
/// Because the payload projection's key set is the presence projection, this
/// field always refines [`crate::observational_field`] with the same `obs` (§F7):
/// it is presence *plus* the pending contents on each observed channel.
pub fn payload_field(lts: &Lts, obs: &[Name]) -> Field {
    observational_field_by(lts, |state| project_payload(state, obs))
}
