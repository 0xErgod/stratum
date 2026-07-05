//! Event-structure layer, phase 2: the **trace** of a run.
//!
//! A run ([`crate::run_events`]) is a *sequence* of events, but that order is
//! partly incidental — the calculus forced some of it and the sequence invented
//! the rest. A [`Trace`] keeps only the order the term forced: the labelled
//! partial order `(events, ≤)` where `≤` is the reflexive-transitive closure of
//! *dependency*, and dependency is read straight off provenance — an event
//! depends on the producers of the two occurrences it consumed.
//!
//! Nothing here adds semantics; it is pure bookkeeping over the [`Event`]s phase
//! 1 produces:
//!
//! - [`Trace::from_run`] turns a run into `(events, covering-relation)`.
//! - [`Trace::linearizations`] lists every total order extending `≤` — the run's
//!   own order is one of them, and they are exactly the runs the trace stands
//!   for.
//! - [`Trace::key`] is the trace's identity as a *set* of events, which phase 3
//!   uses to collapse interleavings.
//! - [`Trace::to_ascii`] / [`Trace::to_dot`] render it: a series-parallel
//!   one-liner where possible (`a ; (b ∥ c) ; d`), else an honest poset marker;
//!   and the Hasse diagram (covering edges only) as Graphviz.

use std::collections::{BTreeSet, HashMap, HashSet};

use stratum_core::{Name, Proc};

use crate::event::{enabled_events, initial_state, Tagged};
use crate::{escape, has_var_channel, mentions_channel, Event, EventKey};

/// The trace of a run: a labelled partial order over events.
///
/// `events` holds the event identities; `leq` is the **covering relation** (the
/// Hasse edges) as index pairs `(a, b)` meaning `a ⋖ b`. The full order `≤` is
/// the reflexive-transitive closure of `leq`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace {
    events: Vec<EventKey>,
    leq: Vec<(usize, usize)>,
}

impl Trace {
    /// Build the trace of a run.
    ///
    /// Dependency is `e' D e` iff `e` consumed an occurrence `e'` produced; `≤`
    /// is `D*`. The stored `leq` is the transitive reduction of `D` (the covering
    /// relation), so redundant edges implied by a longer chain are dropped.
    #[must_use]
    pub fn from_run(events: &[Event]) -> Trace {
        let keys: Vec<EventKey> = events.iter().map(|e| e.key.clone()).collect();
        let n = keys.len();
        let idx: HashMap<EventKey, usize> = keys
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, k)| (k, i))
            .collect();

        // Direct dependency edges: each event on the producer of each occurrence
        // it consumed (deduped; the two occurrences can share a producer).
        let mut direct: BTreeSet<(usize, usize)> = BTreeSet::new();
        for (i, e) in events.iter().enumerate() {
            for occ in [&e.key.out, &e.key.inp] {
                if let Some(pk) = occ.producer() {
                    debug_assert!(
                        idx.contains_key(pk),
                        "a consumed occurrence's producer must be an earlier event of the run"
                    );
                    if let Some(&p) = idx.get(pk) {
                        direct.insert((p, i));
                    }
                }
            }
        }

        let leq = covering_relation(n, &direct);
        Trace { events: keys, leq }
    }

    /// The events, in the run's original order.
    #[must_use]
    pub fn events(&self) -> &[EventKey] {
        &self.events
    }

    /// The covering relation (Hasse edges) as index pairs into [`Trace::events`].
    #[must_use]
    pub fn covering(&self) -> &[(usize, usize)] {
        &self.leq
    }

    /// The number of events.
    #[must_use]
    pub fn len(&self) -> usize {
        self.events.len()
    }

    /// Whether the trace has no events (a terminal start term).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }

    /// The trace's identity as a *set* of events. Two runs are the same trace iff
    /// they fire the same events; phase 3 dedups on this.
    #[must_use]
    pub fn key(&self) -> BTreeSet<EventKey> {
        self.events.iter().cloned().collect()
    }

    /// Every linearization: total orders on the events extending `≤`, each as the
    /// event sequence it lists. The run's own order is among them.
    ///
    /// Exponential in the number of concurrent events by nature; intended for
    /// small traces and for checking that a computation is well-defined (equal
    /// across all of them).
    pub fn linearizations(&self) -> impl Iterator<Item = Vec<EventKey>> {
        let n = self.events.len();
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
        for &(a, b) in &self.leq {
            preds[b].push(a);
        }
        let mut orders: Vec<Vec<usize>> = Vec::new();
        extend(n, &preds, &mut vec![false; n], &mut Vec::new(), &mut orders);
        let events = self.events.clone();
        orders
            .into_iter()
            .map(move |o| o.into_iter().map(|i| events[i].clone()).collect())
    }

    /// A one-line rendering: a series-parallel expression (`;` = then, `∥` =
    /// concurrent) when the order is series-parallel, else `(poset, N events)`.
    /// Event labels are drawn from each event's channel via `label`.
    #[must_use]
    pub fn to_ascii(&self, label: impl Fn(&Name) -> String) -> String {
        if self.events.is_empty() {
            return "(empty)".to_string();
        }
        let reach = closure(self.events.len(), self.leq.iter().copied());
        let all: Vec<usize> = (0..self.events.len()).collect();
        match decompose(&all, &reach) {
            Some(sp) => render_sp(&sp, &self.events, &label, " ; ", " ∥ "),
            None => format!("(poset, {} events)", self.events.len()),
        }
    }

    /// The LaTeX sibling of [`Trace::to_ascii`]: a series-parallel expression
    /// with `\cdot`/`\parallel` (math mode), else a `\text{…}` poset marker.
    #[must_use]
    pub fn to_latex(&self, label: impl Fn(&Name) -> String) -> String {
        if self.events.is_empty() {
            return r"\varnothing".to_string();
        }
        let reach = closure(self.events.len(), self.leq.iter().copied());
        let all: Vec<usize> = (0..self.events.len()).collect();
        match decompose(&all, &reach) {
            Some(sp) => render_sp(&sp, &self.events, &label, r" \cdot ", r" \parallel "),
            None => format!(r"\text{{(poset, {} events)}}", self.events.len()),
        }
    }

    /// The Hasse diagram as Graphviz DOT: one node per event (labelled by its
    /// channel via `label`), one edge per covering pair.
    #[must_use]
    pub fn to_dot(&self, label: impl Fn(&Name) -> String) -> String {
        let mut s = String::from("digraph trace {\n  rankdir=TB;\n");
        for (i, e) in self.events.iter().enumerate() {
            s.push_str(&format!(
                "  e{i} [label=\"{}\"];\n",
                escape(&label(&e.channel))
            ));
        }
        for &(a, b) in &self.leq {
            s.push_str(&format!("  e{a} -> e{b};\n"));
        }
        s.push_str("}\n");
        s
    }

    /// The projection onto the events an agent can see: keep the events
    /// satisfying `keep`, ordered by the **induced** causal order (`a ≤ b` in the
    /// projection iff `a ≤ b` here). Two traces with the same projection are ones
    /// the agent cannot tell apart — the raw material of knowledge.
    #[must_use]
    pub fn project(&self, keep: impl Fn(&EventKey) -> bool) -> Trace {
        let reach = closure(self.events.len(), self.leq.iter().copied());
        let kept: Vec<usize> = (0..self.events.len())
            .filter(|&i| keep(&self.events[i]))
            .collect();
        let events: Vec<EventKey> = kept.iter().map(|&i| self.events[i].clone()).collect();
        // The full induced order over the kept events, then reduce to covering.
        let mut direct = BTreeSet::new();
        for (na, &oa) in kept.iter().enumerate() {
            for (nb, &ob) in kept.iter().enumerate() {
                if na != nb && reach[oa][ob] {
                    direct.insert((na, nb));
                }
            }
        }
        let leq = covering_relation(events.len(), &direct);
        Trace { events, leq }
    }
}

/// The set of traces of `start` — its behaviour as a quotient of its runs.
///
/// Explores **every** branch of the reduction (all interleavings and all
/// choices), turns each maximal run into a [`Trace`], and deduplicates on
/// [`Trace::key`]. Interleavings collapse for free: two orderings of the same
/// independent events fire the same event *set*, so they share a key and count
/// once. Genuine branches (a race, a different receiver) fire different events,
/// so they stay distinct.
///
/// This is the *correctness* path: it materializes the `n!` interleavings before
/// the dedup folds them away. `max_events` bounds any single run and `max_traces`
/// the result; the boolean is `true` when either bound cut the exploration short
/// (as [`crate::Lts::is_truncated`]).
#[must_use]
pub fn traces(start: &Proc, max_events: usize, max_traces: usize) -> (Vec<Trace>, bool) {
    let (out, truncated, _) = enumerate(start, max_events, max_traces, false);
    (out, truncated)
}

/// The trace-set of `start` under a **trace-faithful persistent-set reduction**.
///
/// Identical result to [`traces`], but at each state, when some event is
/// independent of every other enabled one and *future-stable* (no other
/// component could ever present a partner on its channel — as in the barb POR of
/// [`crate::Lts::explore_por`], but with every `Comm` treated as relevant), only
/// that event is fired and the rest are deferred. This prunes the redundant
/// interleavings of independent events *before* generating them, rather than
/// deduplicating them afterward. Genuine branches (conflicts) never satisfy the
/// condition, so they are always fully expanded.
///
/// For terminating profiles the trace-set is exactly [`traces`]'s; a
/// [`por.rs`](../../tests/por.rs)-style differential test pins this. (For a
/// non-terminating profile both paths truncate at `max_events`; the reduction
/// carries no cycle proviso, so faithfulness there is best-effort.)
#[must_use]
pub fn traces_por(start: &Proc, max_events: usize, max_traces: usize) -> (Vec<Trace>, bool) {
    let (out, truncated, _) = enumerate(start, max_events, max_traces, true);
    (out, truncated)
}

/// The shared enumeration core. Returns the trace-set, the truncation flag, and
/// the number of maximal runs explored (before dedup) — the last exposes the
/// interleaving reduction to tests.
pub(crate) fn enumerate(
    start: &Proc,
    max_events: usize,
    max_traces: usize,
    por: bool,
) -> (Vec<Trace>, bool, usize) {
    let mut e = Enumerator {
        seen: HashSet::new(),
        out: Vec::new(),
        truncated: false,
        max_events,
        max_traces,
        por,
        runs: 0,
    };
    e.dfs(&initial_state(start), &mut Vec::new());
    (e.out, e.truncated, e.runs)
}

/// Depth-first enumeration state for [`traces`] / [`traces_por`].
struct Enumerator {
    seen: HashSet<BTreeSet<EventKey>>,
    out: Vec<Trace>,
    truncated: bool,
    max_events: usize,
    max_traces: usize,
    por: bool,
    runs: usize,
}

impl Enumerator {
    /// Explore the events firable from `state`, extending `run`. On reaching a
    /// terminal state, record the maximal run's trace (deduped on its key). Under
    /// `por`, a valid singleton persistent set replaces the full fan-out.
    /// Recursion depth is bounded by `max_events`.
    fn dfs(&mut self, state: &[Tagged], run: &mut Vec<Event>) {
        let enabled = enabled_events(state);
        if enabled.is_empty() {
            self.runs += 1;
            let t = Trace::from_run(run);
            if self.seen.insert(t.key()) {
                if self.out.len() < self.max_traces {
                    self.out.push(t);
                } else {
                    self.truncated = true; // a distinct trace we could not keep
                }
            }
            return;
        }
        if run.len() >= self.max_events {
            self.truncated = true; // a run longer than the bound was cut
            return;
        }
        let chosen: Vec<usize> = match self.por.then(|| singleton_persistent(state, &enabled)) {
            Some(Some(a)) => vec![a],          // a valid singleton persistent set
            _ => (0..enabled.len()).collect(), // full expansion
        };
        for k in chosen {
            let (ev, next) = &enabled[k];
            run.push(ev.clone());
            self.dfs(next, run);
            run.pop();
        }
    }
}

/// A single event that forms a persistent set at `state`, if one exists: it must
/// be **independent** of every other enabled event (disjoint consumed occurrences
/// and a distinct firing channel) and **future-stable** (no *other* component
/// could ever present a communication on its channel, over-approximated by
/// forbidding a variable in any channel position or any mention of the channel).
/// Firing only such an event preserves every trace. Deliberately conservative:
/// when in doubt it returns `None`, forgoing reduction, never soundness.
fn singleton_persistent(state: &[Tagged], enabled: &[(Event, Vec<Tagged>)]) -> Option<usize> {
    'candidate: for (a, (ea, _)) in enabled.iter().enumerate() {
        for (b, (eb, _)) in enabled.iter().enumerate() {
            if a == b {
                continue;
            }
            let shares_occurrence = ea.key.out == eb.key.out
                || ea.key.out == eb.key.inp
                || ea.key.inp == eb.key.out
                || ea.key.inp == eb.key.inp;
            // Channels are `≡N`-canonical, so `==` is channel equality.
            if shares_occurrence || ea.key.channel == eb.key.channel {
                continue 'candidate;
            }
        }
        let stable = state.iter().all(|(p, occ)| {
            *occ == ea.key.out
                || *occ == ea.key.inp
                || (!has_var_channel(p) && !mentions_channel(p, &ea.key.channel))
        });
        if stable {
            return Some(a);
        }
    }
    None
}

/// The covering relation (Hasse edges) of a dependency set: the transitive
/// reduction of `direct` — each `(a, b)` in `direct` with no strict intermediate
/// `c` (`a ≤ c ≤ b`). Shared by [`Trace::from_run`] and the event structure.
pub(crate) fn covering_relation(
    n: usize,
    direct: &BTreeSet<(usize, usize)>,
) -> Vec<(usize, usize)> {
    let reach = closure(n, direct.iter().copied());
    let mut leq = Vec::new();
    for &(a, b) in direct {
        let redundant = (0..n).any(|c| c != a && c != b && reach[a][c] && reach[c][b]);
        if !redundant {
            leq.push((a, b));
        }
    }
    leq
}

/// Transitive closure of `edges` over `n` nodes, as a reachability matrix
/// (`r[i][j]` = a directed path `i → … → j` of length ≥ 1 exists).
#[allow(clippy::needless_range_loop)] // Floyd–Warshall reads across rows by index
pub(crate) fn closure(n: usize, edges: impl Iterator<Item = (usize, usize)>) -> Vec<Vec<bool>> {
    let mut r = vec![vec![false; n]; n];
    for (a, b) in edges {
        r[a][b] = true;
    }
    for k in 0..n {
        for i in 0..n {
            if r[i][k] {
                for j in 0..n {
                    if r[k][j] {
                        r[i][j] = true;
                    }
                }
            }
        }
    }
    r
}

/// Enumerate every topological order of the DAG whose predecessors are `preds`,
/// by placing any node all of whose predecessors are already placed.
fn extend(
    n: usize,
    preds: &[Vec<usize>],
    placed: &mut [bool],
    current: &mut Vec<usize>,
    out: &mut Vec<Vec<usize>>,
) {
    if current.len() == n {
        out.push(current.clone());
        return;
    }
    for v in 0..n {
        if !placed[v] && preds[v].iter().all(|&p| placed[p]) {
            placed[v] = true;
            current.push(v);
            extend(n, preds, placed, current, out);
            current.pop();
            placed[v] = false;
        }
    }
}

/// A series-parallel decomposition of a sub-poset.
enum Sp {
    Leaf(usize),
    Series(Vec<Sp>),
    Parallel(Vec<Sp>),
}

/// Decompose the sub-poset on `nodes` (global indices; `reach` is the global
/// reachability matrix) into a series-parallel expression, or `None` when it
/// contains the N/`P4` obstruction and is therefore not series-parallel.
///
/// Parallel factors are the connected components of the *comparability* graph;
/// series factors are the connected components of the *incomparability* graph
/// (which are then totally ordered). When both graphs are connected on a set of
/// >1 element, the poset is not series-parallel.
fn decompose(nodes: &[usize], reach: &[Vec<bool>]) -> Option<Sp> {
    if nodes.len() == 1 {
        return Some(Sp::Leaf(nodes[0]));
    }
    let comparable = |a: usize, b: usize| reach[a][b] || reach[b][a];

    let comp = components(nodes, comparable);
    if comp.len() > 1 {
        let kids: Option<Vec<Sp>> = comp.iter().map(|c| decompose(c, reach)).collect();
        return Some(Sp::Parallel(kids?));
    }

    let incomp = components(nodes, |a, b| !comparable(a, b));
    if incomp.len() > 1 {
        let mut blocks = incomp;
        // Series factors are totally ordered: one block is entirely below another.
        blocks.sort_by(|x, y| {
            if reach[x[0]][y[0]] {
                std::cmp::Ordering::Less
            } else {
                std::cmp::Ordering::Greater
            }
        });
        let kids: Option<Vec<Sp>> = blocks.iter().map(|c| decompose(c, reach)).collect();
        return Some(Sp::Series(kids?));
    }

    None
}

/// Connected components of the graph on `nodes` whose edges are `related` pairs.
/// Returns each component as a sorted list of the original (global) indices.
fn components(nodes: &[usize], related: impl Fn(usize, usize) -> bool) -> Vec<Vec<usize>> {
    let mut seen = vec![false; nodes.len()];
    let mut comps = Vec::new();
    for start in 0..nodes.len() {
        if seen[start] {
            continue;
        }
        seen[start] = true;
        let mut stack = vec![start];
        let mut comp = Vec::new();
        while let Some(u) = stack.pop() {
            comp.push(nodes[u]);
            for (v, s) in seen.iter_mut().enumerate() {
                if !*s && related(nodes[u], nodes[v]) {
                    *s = true;
                    stack.push(v);
                }
            }
        }
        comp.sort_unstable();
        comps.push(comp);
    }
    comps
}

/// Render a series-parallel expression, parenthesizing any composite child, with
/// `ser`/`par` as the series/parallel separators (so the same tree renders as
/// ASCII `a ; (b ∥ c)` or LaTeX `a \cdot (b \parallel c)`).
fn render_sp(
    sp: &Sp,
    events: &[EventKey],
    label: &dyn Fn(&Name) -> String,
    ser: &str,
    par: &str,
) -> String {
    let child = |c: &Sp| match c {
        Sp::Leaf(_) => render_sp(c, events, label, ser, par),
        _ => format!("({})", render_sp(c, events, label, ser, par)),
    };
    match sp {
        Sp::Leaf(i) => label(&events[*i].channel),
        Sp::Series(cs) => cs.iter().map(child).collect::<Vec<_>>().join(ser),
        Sp::Parallel(cs) => cs.iter().map(child).collect::<Vec<_>>().join(par),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::ch;
    use crate::{format_name, run_events, OccKey};
    use stratum_core::term::{drop_, input, lift, par, zero};
    use stratum_core::Name;

    #[test]
    fn causal_chain_is_totally_ordered() {
        // x⟨|a⟨|0|⟩|⟩ | x(y).*y | a(z).0 — the a-event depends on the x-event.
        let x = ch(1);
        let a = ch(2);
        let p = par([
            lift(x.clone(), lift(a.clone(), zero())),
            input(x, drop_),
            input(a, |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        let t = Trace::from_run(&evs);
        assert_eq!(t.len(), 2);
        assert_eq!(t.covering().len(), 1); // one Hasse edge
        assert_eq!(t.linearizations().count(), 1); // fully forced
        let s = t.to_ascii(format_name);
        assert!(s.contains(" ; "), "expected a series form, got {s:?}");
        assert!(!s.contains(" ∥ "));
    }

    #[test]
    fn concurrent_pair_is_one_trace_two_linearizations() {
        // a⟨|0|⟩ | a(x).0 | b⟨|0|⟩ | b(y).0 — independent reactions.
        let a = ch(1);
        let b = ch(2);
        let p = par([
            lift(a.clone(), zero()),
            input(a, |_| zero()),
            lift(b.clone(), zero()),
            input(b, |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        let t = Trace::from_run(&evs);
        assert_eq!(t.len(), 2);
        assert_eq!(t.covering().len(), 0); // no forced order
        assert_eq!(t.linearizations().count(), 2);
        let s = t.to_ascii(format_name);
        assert!(s.contains(" ∥ "), "expected a parallel form, got {s:?}");
        assert!(!s.contains(" ; "));
    }

    #[test]
    fn well_defined_quantity_is_constant_across_linearizations() {
        // The multiset of channels is order-insensitive, so it must agree on
        // every linearization — the one-swap criterion in miniature.
        let a = ch(1);
        let b = ch(2);
        let p = par([
            lift(a.clone(), zero()),
            input(a, |_| zero()),
            lift(b.clone(), zero()),
            input(b, |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        let t = Trace::from_run(&evs);
        let sorted_labels = |lin: &Vec<EventKey>| {
            let mut cs: Vec<Name> = lin.iter().map(|k| k.channel.clone()).collect();
            cs.sort();
            cs
        };
        let lins: Vec<_> = t.linearizations().collect();
        assert!(lins.len() >= 2);
        let first = sorted_labels(&lins[0]);
        assert!(lins.iter().all(|l| sorted_labels(l) == first));
    }

    #[test]
    fn fork_renders_series_of_parallel() {
        // x⟨|0|⟩ | x(y).(a⟨|0|⟩ | b⟨|0|⟩) | a(z).0 | b(w).0
        // The x-Comm unfreezes a and b, which then react independently:
        // x ; (a ∥ b).
        let x = ch(1);
        let a = ch(2);
        let b = ch(3);
        let p = par([
            lift(x.clone(), zero()),
            input(x, move |_| {
                par([lift(a.clone(), zero()), lift(b.clone(), zero())])
            }),
            input(ch(2), |_| zero()),
            input(ch(3), |_| zero()),
        ]);
        let (evs, _) = run_events(&p, 10);
        let t = Trace::from_run(&evs);
        assert_eq!(t.len(), 3);
        let s = t.to_ascii(format_name);
        assert!(s.contains(" ; "), "got {s:?}");
        assert!(s.contains(" ∥ "), "got {s:?}");
        assert!(
            s.contains('('),
            "parallel factor should be parenthesized: {s:?}"
        );
    }

    #[test]
    fn non_series_parallel_poset_falls_back() {
        // The N poset: a<c, b<c, b<d — not series-parallel.
        let mk = |c: u64| EventKey {
            channel: ch(c),
            message: ch(0),
            out: OccKey::Initial(c as usize),
            inp: OccKey::Initial(100 + c as usize),
        };
        let t = Trace {
            events: vec![mk(1), mk(2), mk(3), mk(4)], // a, b, c, d
            leq: vec![(0, 2), (1, 2), (1, 3)],
        };
        assert_eq!(t.to_ascii(format_name), "(poset, 4 events)");
    }

    #[test]
    fn projection_keeps_induced_order() {
        // x ; a (a causal chain). Projecting onto {a} drops x and its edge;
        // projecting onto both keeps the single covering edge.
        let chain = par([
            lift(ch(1), lift(ch(2), zero())),
            input(ch(1), drop_),
            input(ch(2), |_| zero()),
        ]);
        let (evs, _) = run_events(&chain, 10);
        let t = Trace::from_run(&evs);
        let onto_a = t.project(|e| stratum_core::name_equiv(&e.channel, &ch(2)));
        assert_eq!(onto_a.len(), 1);
        assert_eq!(onto_a.covering().len(), 0);
        let both = t.project(|_| true);
        assert_eq!(both.len(), 2);
        assert_eq!(both.covering().len(), 1);
    }

    // --- traces() enumeration ---

    type LabelRun = Vec<(Name, Name)>;

    fn labels_of(lin: &[EventKey]) -> LabelRun {
        lin.iter()
            .map(|k| (k.channel.clone(), k.message.clone()))
            .collect()
    }

    /// The set of label-sequences of every linearization of every trace.
    fn trace_label_runs(ts: &[Trace]) -> BTreeSet<LabelRun> {
        ts.iter()
            .flat_map(Trace::linearizations)
            .map(|l| labels_of(&l))
            .collect()
    }

    /// The set of maximal label-runs of the full LTS (DFS to terminal states).
    /// Assumes an **acyclic** LTS (the round-trip inputs are replication-free); a
    /// replicating term would need a visited guard to avoid looping.
    fn lts_label_runs(lts: &crate::Lts) -> BTreeSet<LabelRun> {
        fn go(lts: &crate::Lts, s: usize, path: &mut LabelRun, out: &mut BTreeSet<LabelRun>) {
            let ts = lts.transitions(s);
            if ts.is_empty() {
                out.insert(path.clone());
                return;
            }
            for t in ts {
                path.push((t.label.clone(), t.message.clone()));
                go(lts, t.target, path, out);
                path.pop();
            }
        }
        let mut out = BTreeSet::new();
        go(lts, lts.initial(), &mut Vec::new(), &mut out);
        out
    }

    #[test]
    fn terminal_start_is_one_empty_trace() {
        let (ts, truncated) = traces(&zero(), 10, 10);
        assert!(!truncated);
        assert_eq!(ts.len(), 1);
        assert!(ts[0].is_empty());
    }

    #[test]
    fn interleaving_absorbed_branching_kept() {
        let a = ch(1);
        let b = ch(2);
        // Diamond: two independent reactions collapse to ONE trace (2 linearizations).
        let diamond = par([
            lift(a.clone(), zero()),
            input(a.clone(), |_| zero()),
            lift(b.clone(), zero()),
            input(b.clone(), |_| zero()),
        ]);
        let (ts, _) = traces(&diamond, 10, 100);
        assert_eq!(ts.len(), 1);
        assert_eq!(ts[0].linearizations().count(), 2);

        // Chain: dependent reactions -> ONE trace, ONE linearization.
        let chain = par([
            lift(ch(1), lift(ch(2), zero())),
            input(ch(1), drop_),
            input(ch(2), |_| zero()),
        ]);
        let (ts2, _) = traces(&chain, 10, 100);
        assert_eq!(ts2.len(), 1);
        assert_eq!(ts2[0].linearizations().count(), 1);

        // Race: one output, two receivers -> TWO distinct traces (conflict).
        let a2 = ch(2);
        let b2 = ch(3);
        let race = par([
            lift(ch(1), zero()),
            input(ch(1), move |_| lift(a2.clone(), zero())),
            input(ch(1), move |_| lift(b2.clone(), zero())),
        ]);
        let (ts3, _) = traces(&race, 10, 100);
        assert_eq!(ts3.len(), 2);
    }

    #[test]
    fn unfolding_round_trip_matches_full_lts() {
        // A causal chain (x ; a) concurrent with an independent reaction (b):
        // exercises both concurrency and causality. Every linearization of every
        // trace must equal, as a label sequence, a maximal run of the full LTS.
        let mk = || {
            par([
                lift(ch(1), lift(ch(2), zero())), // x!(a!0)
                input(ch(1), drop_),              // x(y).*y
                input(ch(2), |_| zero()),         // a(z).0
                lift(ch(3), zero()),              // b!0
                input(ch(3), |_| zero()),         // b(y).0
            ])
        };
        let (ts, truncated) = traces(&mk(), 20, 1000);
        assert!(!truncated);
        let lts = crate::Lts::explore(&mk(), 1000);
        assert_eq!(trace_label_runs(&ts), lts_label_runs(&lts));
    }

    // --- traces_por() faithfulness ---

    /// `n` independent reaction pairs on distinct channels — the archetypal
    /// interleaving blow-up (`n!` runs, one trace).
    fn n_independent(n: u64) -> Proc {
        let mut comps = Vec::new();
        for i in 0..n {
            let c = ch(i + 1);
            comps.push(lift(c.clone(), zero()));
            comps.push(input(c, |_| zero()));
        }
        par(comps)
    }

    /// A varied corpus exercising concurrency, causality, conflict, reflective
    /// forks, inherited conflict, wide independence, and a terminal term.
    fn corpus() -> Vec<Proc> {
        vec![
            // diamond
            par([
                lift(ch(1), zero()),
                input(ch(1), |_| zero()),
                lift(ch(2), zero()),
                input(ch(2), |_| zero()),
            ]),
            // reflective chain
            par([
                lift(ch(1), lift(ch(2), zero())),
                input(ch(1), drop_),
                input(ch(2), |_| zero()),
            ]),
            // race
            par([
                lift(ch(1), zero()),
                input(ch(1), |_| zero()),
                input(ch(1), |_| zero()),
            ]),
            // reflective fork: x ; (a ∥ b)
            par([
                lift(ch(1), zero()),
                input(ch(1), |_| par([lift(ch(2), zero()), lift(ch(3), zero())])),
                input(ch(2), |_| zero()),
                input(ch(3), |_| zero()),
            ]),
            // race with a downstream reaction (inherited conflict)
            par([
                lift(ch(1), zero()),
                input(ch(1), |_| lift(ch(2), zero())),
                input(ch(1), |_| zero()),
                input(ch(2), |_| zero()),
            ]),
            n_independent(3),
            n_independent(4),
            zero(),
        ]
    }

    #[test]
    fn por_matches_full_on_corpus() {
        for (i, p) in corpus().iter().enumerate() {
            let full: BTreeSet<BTreeSet<EventKey>> =
                traces(p, 30, 100_000).0.iter().map(Trace::key).collect();
            let por: BTreeSet<BTreeSet<EventKey>> = traces_por(p, 30, 100_000)
                .0
                .iter()
                .map(Trace::key)
                .collect();
            assert_eq!(full, por, "corpus[{i}]: trace-set diverged under POR");
        }
    }

    #[test]
    fn por_reduces_independent_interleavings() {
        // Four independent reactions: the full path explores all 4! = 24
        // interleavings; POR explores exactly one. Both yield the one trace.
        let p = n_independent(4);
        let (full, _, full_runs) = enumerate(&p, 30, 100_000, false);
        let (por, _, por_runs) = enumerate(&p, 30, 100_000, true);
        assert_eq!(full.len(), 1);
        assert_eq!(por.len(), 1);
        assert_eq!(full_runs, 24);
        assert_eq!(por_runs, 1);
    }
}
