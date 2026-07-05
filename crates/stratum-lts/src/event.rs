//! Event-structure layer, phase 1: the **instrumented COMM stepper**.
//!
//! [`crate::Lts`] records *states and transitions*; it forgets which occurrence
//! of a component each `Comm` consumed, and so cannot say *why* one reaction had
//! to precede another. This module keeps that information. It steps a ρ-calculus
//! term while tagging every active parallel component with its **provenance** —
//! where it was born — so that each firing becomes an [`Event`] carrying an
//! order-independent identity.
//!
//! # What pins an event down
//!
//! An event is one `Comm` firing. Its identity is *not* its label and *not* its
//! position in a run — two firings of the same `(channel, message)` are still
//! distinct, and a firing keeps its identity when the run is reordered. What
//! individuates it is the pair of **occurrences it consumes**: one output
//! component and one input component, each named by where it was born.
//!
//! - [`OccKey::Initial`] — a component of the start term, by flatten-index.
//! - [`OccKey::Born`] — the `k`-th component of some earlier event's residue.
//!
//! Because a `Born` occurrence names its producer, and that producer's key names
//! *its* consumed occurrences, an [`EventKey`] is a finite tree grounding out at
//! `Initial` leaves — exactly the event's causal history. Two runs that fire the
//! same event compute the same key, no matter the order.
//!
//! # Why this also captures reflective causality
//!
//! A `Comm` substitutes the reified message `⌜Q⌝` into the receiver body, and a
//! `Drop` of that name unfreezes `Q` — so the residue's components are *born*
//! from the firing. If a later event consumes one of them, its `out`/`inp` key
//! points back at the producer, recording the dependency with no special rule
//! for reflection: causality is simply "I consumed what you produced".
//!
//! Provenance is tracked on the **nominal** term. Canonicalization reuses de
//! Bruijn `0` at every binder and fuses `≡`-equal subterms, which would collapse
//! distinct occurrences; names are canonicalized only for `≡N` matching and for
//! the label carried on the key.

use stratum_core::{canonicalize_name, name_equiv, subst_semantic, Name, Proc};
use tracing::{debug, debug_span, trace};

use crate::flatten;

/// The birthplace of an active parallel component — an event's occurrence
/// identity, independent of firing order.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum OccKey {
    /// The `i`-th component of the start term (in flatten order).
    Initial(usize),
    /// The `k`-th component (in flatten order) of the residue produced by the
    /// event identified by the boxed key.
    Born(Box<EventKey>, usize),
}

impl OccKey {
    /// The event that produced this occurrence, or `None` when it was present in
    /// the start term. This is the generator of the causal order: an event
    /// depends on the producers of the two occurrences it consumes.
    #[must_use]
    pub fn producer(&self) -> Option<&EventKey> {
        match self {
            OccKey::Initial(_) => None,
            OccKey::Born(k, _) => Some(k),
        }
    }
}

/// The order-independent identity of a `Comm` firing: what crossed, and the two
/// occurrences it consumed.
///
/// The label is `(channel, message)`; the identity is `(out, inp)`. The `channel`
/// and `message` are `≡N`-canonical, as on [`crate::Transition`].
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EventKey {
    /// The `≡N`-canonical firing channel.
    pub channel: Name,
    /// The `≡N`-canonical transmitted message `⌜Q⌝`.
    pub message: Name,
    /// The output component consumed.
    pub out: OccKey,
    /// The input component consumed.
    pub inp: OccKey,
}

/// A realized event: its identity together with the occurrences it produced, so
/// later events can name it as their producer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Event {
    /// The event's order-independent identity and label.
    pub key: EventKey,
    /// The occurrences flattened out of this firing's residue `P{⌜Q⌝/y}`, each a
    /// [`OccKey::Born`] of `key`.
    pub produces: Vec<OccKey>,
}

/// An active parallel component paired with its provenance tag.
pub(crate) type Tagged = (Proc, OccKey);

/// The instrumented start state: the start term's active components, each tagged
/// with its [`OccKey::Initial`] flatten-index.
pub(crate) fn initial_state(start: &Proc) -> Vec<Tagged> {
    let mut comps = Vec::new();
    flatten(start, &mut comps);
    comps
        .into_iter()
        .enumerate()
        .map(|(i, p)| (p, OccKey::Initial(i)))
        .collect()
}

/// Every `Comm` firable from `state`, each paired with the instrumented
/// successor state.
///
/// Mirrors [`crate::Lts`]'s redex enumeration but **without** the
/// `(channel, message, target)` deduplication: each distinct `(out, inp)`
/// occurrence pair is a distinct event, even when two share a label. The output
/// and input consumed are dropped from the successor; the residue's components
/// are appended, tagged as [`OccKey::Born`] of the new event.
///
/// Each candidate carries its *full* successor state so a caller that branches
/// (the trace enumeration of later phases) can step any of them; the linear
/// [`run_events`] driver uses only the first.
pub(crate) fn enabled_events(state: &[Tagged]) -> Vec<(Event, Vec<Tagged>)> {
    let mut out = Vec::new();
    for (i, (p_i, out_occ)) in state.iter().enumerate() {
        let Proc::Lift { chan: x0, arg: q } = p_i else {
            continue;
        };
        for (j, (p_j, in_occ)) in state.iter().enumerate() {
            if i == j {
                continue;
            }
            let Proc::Input {
                chan: x1,
                bound,
                body,
            } = p_j
            else {
                continue;
            };
            if !name_equiv(x0, x1) {
                continue;
            }

            // Substitute the *nominal* message ⌜Q⌝ into the receiver, exactly as
            // the Comm rule; canonicalize only for the label on the key.
            let message_nominal = Name::Quote(q.clone());
            let key = EventKey {
                channel: canonicalize_name(x0),
                message: canonicalize_name(&message_nominal),
                out: out_occ.clone(),
                inp: in_occ.clone(),
            };
            let reduced = subst_semantic(body, *bound, &message_nominal);
            let mut born = Vec::new();
            flatten(&reduced, &mut born);
            let produces: Vec<OccKey> = (0..born.len())
                .map(|k| OccKey::Born(Box::new(key.clone()), k))
                .collect();

            let mut next: Vec<Tagged> = state
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != i && *k != j)
                .map(|(_, t)| t.clone())
                .collect();
            next.extend(born.into_iter().zip(produces.iter().cloned()));

            out.push((Event { key, produces }, next));
        }
    }
    out
}

/// Drive a single run from `start`, following the first firable event at each
/// step, and return its events in firing order.
///
/// The boolean is `true` when the run was cut short by `max_events` while more
/// events remained firable (mirroring [`crate::Lts::is_truncated`]), and `false`
/// when the run reached a terminal state on its own.
#[must_use]
pub fn run_events(start: &Proc, max_events: usize) -> (Vec<Event>, bool) {
    let mut state = initial_state(start);
    let mut events = Vec::new();
    loop {
        let enabled = enabled_events(&state);
        trace!(enabled = enabled.len(), fired = events.len(), "stepping");
        if enabled.is_empty() {
            debug!(fired = events.len(), "run complete (terminal)");
            return (events, false);
        }
        if events.len() >= max_events {
            debug!(fired = events.len(), "run truncated (event bound hit)");
            return (events, true);
        }
        let (ev, next) = enabled.into_iter().next().expect("non-empty");
        // A span over the firing carrying the full event: its label and the
        // occurrences it consumed and produced — the trace of *why* the run took
        // this step, silent unless a subscriber is installed.
        let _fired = debug_span!(
            "fired",
            channel = ?ev.key.channel,
            message = ?ev.key.message,
            out = ?ev.key.out,
            inp = ?ev.key.inp,
            produces = ?ev.produces,
        )
        .entered();
        events.push(ev);
        state = next;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::ch;
    use stratum_core::term::{drop_, input, lift, par, zero};

    #[test]
    fn causal_reflective_dependency() {
        // x⟨|a⟨|0|⟩|⟩ | x(y).*y | a(z).0
        // The x-Comm delivers ⌜a⟨|0|⟩⌝; *y drops it, waking a⟨|0|⟩, which the
        // a-Comm then consumes. So the a-event depends on the x-event — purely
        // through reflection.
        let x = ch(1);
        let a = ch(2);
        let p = par([
            lift(x.clone(), lift(a.clone(), zero())),
            input(x, drop_),
            input(a, |_| zero()),
        ]);
        let (evs, truncated) = run_events(&p, 10);
        assert!(!truncated);
        assert_eq!(evs.len(), 2);
        // e2 consumed exactly what e1 produced.
        assert_eq!(evs[1].key.out, evs[0].produces[0]);
        // e1 depends on nothing; e2 depends on e1.
        assert!(evs[0].key.out.producer().is_none());
        assert!(evs[0].key.inp.producer().is_none());
        assert_eq!(evs[1].key.out.producer(), Some(&evs[0].key));
    }

    #[test]
    fn concurrent_events_are_independent() {
        // a⟨|0|⟩ | a(x).0 | b⟨|0|⟩ | b(y).0 — two disjoint reactions.
        let a = ch(1);
        let b = ch(2);
        let p = par([
            lift(a.clone(), zero()),
            input(a, |_| zero()),
            lift(b.clone(), zero()),
            input(b, |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        assert_eq!(evs.len(), 2);
        for e in &evs {
            assert!(e.key.out.producer().is_none());
            assert!(e.key.inp.producer().is_none());
        }
        assert_ne!(evs[0].key, evs[1].key);
    }

    #[test]
    fn racing_inputs_share_the_output_occurrence() {
        // x⟨|0|⟩ | x(y).0 | x(w).0 — one output, two inputs competing.
        let x = ch(1);
        let p = par([
            lift(x.clone(), zero()),
            input(x.clone(), |_| zero()),
            input(x, |_| zero()),
        ]);
        let state = initial_state(&p);
        let enabled = enabled_events(&state);
        assert_eq!(enabled.len(), 2);
        let e0 = &enabled[0].0.key;
        let e1 = &enabled[1].0.key;
        // Same output occurrence -> the two firings are in conflict.
        assert_eq!(e0.out, e1.out);
        assert_ne!(e0.inp, e1.inp);
    }

    #[test]
    fn same_label_distinct_events() {
        // Two independent copies of a⟨|0|⟩ | a(x).0: identical labels, distinct
        // occurrences.
        let a = ch(1);
        let p = par([
            lift(a.clone(), zero()),
            input(a.clone(), |_| zero()),
            lift(a.clone(), zero()),
            input(a, |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        assert_eq!(evs.len(), 2);
        assert_eq!(evs[0].key.channel, evs[1].key.channel);
        assert_eq!(evs[0].key.message, evs[1].key.message);
        assert_ne!(evs[0].key.out, evs[1].key.out);
        assert_ne!(evs[0].key.inp, evs[1].key.inp);
    }
}
