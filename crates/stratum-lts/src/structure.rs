//! Event-structure layer, phase 4: **conflict** and the labelled prime event
//! structure.
//!
//! A single [`crate::Trace`] keeps causality and concurrency but forgets *where*
//! two runs branched. The [`EventStructure`] restores that: it unions all the
//! events a profile can produce into one set and adds a **conflict** relation
//! `#` — the pairs that cannot both occur. The three relations then carry the
//! three phenomena exactly:
//!
//! - `≤` (causality) — an event depends on the producers of what it consumed.
//! - concurrency — incomparable and conflict-free (the diamond that closes).
//! - `#` (branching) — two events that compete for the same occurrence, plus
//!   everything inheriting that conflict upward along `≤`.
//!
//! A **configuration** is a conflict-free, downward-closed set of events; a
//! single trace is a *maximal* configuration, so [`EventStructure::maximal_configurations`]
//! recovers exactly [`crate::traces`].

use std::collections::{BTreeSet, HashMap, HashSet};

use stratum_core::Proc;

use crate::event::{enabled_events, initial_state, Tagged};
use crate::trace::{closure, covering_relation};
use crate::EventKey;

/// A labelled prime event structure: all the events a profile can produce, their
/// causal order, and the conflict between them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EventStructure {
    events: Vec<EventKey>,
    leq: Vec<(usize, usize)>,      // covering relation (Hasse edges)
    conflict: Vec<(usize, usize)>, // immediate conflict, stored with a < b
    truncated: bool,
}

/// Build the event structure of `start`.
///
/// Explores every branch of the reduction, interning each fired event by its
/// [`EventKey`] into a global set and recording the dependency edges. `≤` is the
/// covering relation of those dependencies; immediate `#` is the pairs of events
/// consuming a common output or input occurrence. `max_events` bounds the depth
/// of any single run.
#[must_use]
pub fn event_structure(start: &Proc, max_events: usize) -> EventStructure {
    let mut c = Collector {
        idx: HashMap::new(),
        events: Vec::new(),
        direct: BTreeSet::new(),
        truncated: false,
        max_events,
    };
    c.collect(&initial_state(start), 0);

    let n = c.events.len();
    let leq = covering_relation(n, &c.direct);

    // Immediate conflict: two distinct events consuming a common occurrence.
    // Output- and input-occurrences are disjoint (a component is a Lift xor an
    // Input), so a shared `out` or a shared `inp` is the whole relation.
    let mut conflict = Vec::new();
    for i in 0..n {
        for j in (i + 1)..n {
            if c.events[i].out == c.events[j].out || c.events[i].inp == c.events[j].inp {
                conflict.push((i, j));
            }
        }
    }

    EventStructure {
        events: c.events,
        leq,
        conflict,
        truncated: c.truncated,
    }
}

/// DFS collector for [`event_structure`]: interns events globally and records
/// dependency edges as it explores every branch.
struct Collector {
    idx: HashMap<EventKey, usize>,
    events: Vec<EventKey>,
    direct: BTreeSet<(usize, usize)>,
    truncated: bool,
    max_events: usize,
}

impl Collector {
    /// The global index of `key`, assigning a fresh one on first sighting.
    fn intern(&mut self, key: &EventKey) -> usize {
        if let Some(&i) = self.idx.get(key) {
            return i;
        }
        let i = self.events.len();
        self.idx.insert(key.clone(), i);
        self.events.push(key.clone());
        i
    }

    fn collect(&mut self, state: &[Tagged], depth: usize) {
        let enabled = enabled_events(state);
        if enabled.is_empty() {
            return;
        }
        if depth >= self.max_events {
            self.truncated = true;
            return;
        }
        for (ev, next) in enabled {
            let i = self.intern(&ev.key);
            // Each occurrence's producer fired earlier on this path, so it is
            // already interned; record the dependency edge.
            for occ in [&ev.key.out, &ev.key.inp] {
                if let Some(pk) = occ.producer() {
                    debug_assert!(
                        self.idx.contains_key(pk),
                        "a consumed occurrence's producer must be interned before its consumer"
                    );
                    if let Some(&p) = self.idx.get(pk) {
                        self.direct.insert((p, i));
                    }
                }
            }
            self.collect(&next, depth + 1);
        }
    }
}

impl EventStructure {
    /// The events.
    #[must_use]
    pub fn events(&self) -> &[EventKey] {
        &self.events
    }

    /// The covering relation (Hasse edges) as index pairs into [`Self::events`].
    #[must_use]
    pub fn covering(&self) -> &[(usize, usize)] {
        &self.leq
    }

    /// The **immediate** conflict pairs (each stored with the smaller index
    /// first). The full relation is the upward closure under `≤`; query it with
    /// [`Self::in_conflict`].
    #[must_use]
    pub fn conflict(&self) -> &[(usize, usize)] {
        &self.conflict
    }

    /// Whether exploration hit the event bound (a fragment of a larger space).
    #[must_use]
    pub fn is_truncated(&self) -> bool {
        self.truncated
    }

    /// Whether events `a` and `b` are in conflict — immediate, or **inherited**:
    /// `a # b` when some `a₀ ≤ a` and `b₀ ≤ b` are in immediate conflict.
    /// Irreflexive and symmetric.
    #[must_use]
    pub fn in_conflict(&self, a: usize, b: usize) -> bool {
        let reach = closure(self.events.len(), self.leq.iter().copied());
        let below = |x: usize, y: usize| x == y || reach[x][y];
        // Self-conflict cannot arise: an event's causal history is a single
        // conflict-free chain, so no event lies above both endpoints of an
        // immediate conflict; hence `in_conflict(i, i)` is always false.
        self.conflict
            .iter()
            .any(|&(p, q)| (below(p, a) && below(q, b)) || (below(p, b) && below(q, a)))
    }

    /// The maximal configurations — the conflict-free, downward-closed sets that
    /// cannot be extended. These are exactly the profile's traces (as event
    /// sets); see [`crate::traces`].
    #[must_use]
    pub fn maximal_configurations(&self) -> Vec<BTreeSet<EventKey>> {
        let n = self.events.len();
        let mut preds = vec![Vec::new(); n];
        for &(a, b) in &self.leq {
            preds[b].push(a);
        }
        let mut confl = vec![Vec::new(); n];
        for &(i, j) in &self.conflict {
            confl[i].push(j);
            confl[j].push(i);
        }
        let mut seen = HashSet::new();
        let mut out = Vec::new();
        self.grow(&mut vec![false; n], &preds, &confl, &mut seen, &mut out);
        out.into_iter()
            .map(|c| c.into_iter().map(|i| self.events[i].clone()).collect())
            .collect()
    }

    /// Backtracking enumeration of maximal configurations. Because immediate
    /// conflict-freedom plus downward-closure already precludes *inherited*
    /// conflict, the addable test only needs the immediate relation.
    fn grow(
        &self,
        in_c: &mut [bool],
        preds: &[Vec<usize>],
        confl: &[Vec<usize>],
        seen: &mut HashSet<BTreeSet<usize>>,
        out: &mut Vec<BTreeSet<usize>>,
    ) {
        let addable: Vec<usize> = (0..in_c.len())
            .filter(|&e| {
                !in_c[e] && preds[e].iter().all(|&p| in_c[p]) && confl[e].iter().all(|&c| !in_c[c])
            })
            .collect();
        if addable.is_empty() {
            let set: BTreeSet<usize> = (0..in_c.len()).filter(|&i| in_c[i]).collect();
            if seen.insert(set.clone()) {
                out.push(set);
            }
            return;
        }
        for e in addable {
            in_c[e] = true;
            self.grow(in_c, preds, confl, seen, out);
            in_c[e] = false;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::ch;
    use crate::traces;
    use stratum_core::term::{input, lift, par, zero};

    /// The maximal configurations of the event structure must equal the traces.
    fn assert_configs_match_traces(p: &Proc) {
        let es = event_structure(p, 20);
        let configs: BTreeSet<BTreeSet<EventKey>> =
            es.maximal_configurations().into_iter().collect();
        let (ts, _) = traces(p, 20, 1000);
        let keys: BTreeSet<BTreeSet<EventKey>> = ts.iter().map(crate::Trace::key).collect();
        assert_eq!(configs, keys);
    }

    #[test]
    fn race_has_one_immediate_conflict() {
        // x!0 | x(y).a!0 | x(w).b!0 — the output feeds either receiver.
        let a = ch(2);
        let b = ch(3);
        let p = par([
            lift(ch(1), zero()),
            input(ch(1), move |_| lift(a.clone(), zero())),
            input(ch(1), move |_| lift(b.clone(), zero())),
        ]);
        let es = event_structure(&p, 20);
        assert_eq!(es.events().len(), 2);
        assert_eq!(es.conflict().len(), 1);
    }

    #[test]
    fn conflict_is_irreflexive_symmetric_and_inherited() {
        // x!0 | x(y).a!0 | x(w).0 | a(z).0
        // The y-branch fires a downstream a-event; the w-branch does not. So the
        // two x-events conflict immediately, and the a-event (above the y-event)
        // inherits a conflict with the w-event.
        let a = ch(2);
        let p = par([
            lift(ch(1), zero()),
            input(ch(1), move |_| lift(a.clone(), zero())),
            input(ch(1), |_| zero()),
            input(ch(2), |_| zero()),
        ]);
        let es = event_structure(&p, 20);
        let n = es.events().len();
        for i in 0..n {
            assert!(!es.in_conflict(i, i), "conflict must be irreflexive");
        }
        for i in 0..n {
            for j in 0..n {
                assert_eq!(es.in_conflict(i, j), es.in_conflict(j, i), "symmetry");
            }
        }
        let immediate: BTreeSet<(usize, usize)> = es.conflict().iter().copied().collect();
        let inherited = (0..n)
            .any(|i| ((i + 1)..n).any(|j| es.in_conflict(i, j) && !immediate.contains(&(i, j))));
        assert!(inherited, "expected an inherited (non-immediate) conflict");
    }

    #[test]
    fn maximal_configurations_match_traces() {
        let (a, b) = (ch(1), ch(2));
        // Diamond (concurrency).
        assert_configs_match_traces(&par([
            lift(a.clone(), zero()),
            input(a.clone(), |_| zero()),
            lift(b.clone(), zero()),
            input(b.clone(), |_| zero()),
        ]));
        // Chain (causality).
        assert_configs_match_traces(&par([
            lift(ch(1), lift(ch(2), zero())),
            input(ch(1), stratum_core::term::drop_),
            input(ch(2), |_| zero()),
        ]));
        // Race (branching).
        let (a2, b2) = (ch(2), ch(3));
        assert_configs_match_traces(&par([
            lift(ch(1), zero()),
            input(ch(1), move |_| lift(a2.clone(), zero())),
            input(ch(1), move |_| lift(b2.clone(), zero())),
        ]));
        // Terminal.
        assert_configs_match_traces(&zero());
    }
}
