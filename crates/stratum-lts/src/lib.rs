//! # stratum-lts
//!
//! The **trace layer**: a labelled transition system
//! (LTS) built from the ρ-calculus reduction relation of [`stratum_core`].
//!
//! States are canonical processes (so `≡`-congruent processes are the *same*
//! node); transitions are tagged with the `≡N`-canonical channel the `Comm`
//! fired on. This is the explicit graph that the temporal-logic checker and the
//! bisimulation checker (later milestones) consume, and the artifact you inspect
//! to read a system's runs.
//!
//! Because a ρ-calculus state space is in general infinite (replication,
//! unbounded name generation), [`Lts::explore`] is bounded by a maximum number
//! of states and records whether that bound truncated the exploration.
//!
//! ```
//! use stratum_core::term::{input, lift, quote, zero, par};
//! use stratum_lts::Lts;
//!
//! // a⟨|0|⟩ | a(y).0   reduces to   0
//! let a = quote(zero());
//! let sys = par([lift(a.clone(), zero()), input(a, |_| zero())]);
//! let lts = Lts::explore(&sys, 100);
//! assert_eq!(lts.num_states(), 2);      // initial and 0
//! assert_eq!(lts.transitions(lts.initial()).len(), 1);
//! assert!(!lts.is_truncated());
//! ```

use std::collections::{BTreeSet, HashMap, VecDeque};

use stratum_core::{
    canonicalize, canonicalize_name, name_equiv, step_labeled, subst_semantic, Name, Proc,
};

mod event;
mod trace;
pub use event::{run_events, Event, EventKey, OccKey};
pub use trace::Trace;

/// A labelled transition to another state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    /// The `≡N`-canonical channel the `Comm` fired on.
    pub label: Name,
    /// The `≡N`-canonical message transmitted by the `Comm` — the reified name
    /// `⌜Q⌝` bound by the receiver. A first-class observation of the step, not
    /// merely part of the target state.
    pub message: Name,
    /// Index of the target state in the owning [`Lts`].
    pub target: usize,
}

/// A bounded labelled transition system over ρ-calculus reduction.
///
/// State `0` is always the initial state. States are stored in canonical form;
/// [`Lts::explore`] deduplicates them up to structural congruence.
#[derive(Clone, Debug)]
pub struct Lts {
    states: Vec<Proc>,
    index: HashMap<Proc, usize>,
    transitions: Vec<Vec<Transition>>,
    truncated: bool,
}

impl Lts {
    /// Explore the reduction graph from `start`, breadth-first, up to
    /// `max_states` distinct states.
    ///
    /// The frontier is stepped as nominal representatives while canonical forms
    /// are the identity keys (a canonical term reuses de Bruijn index `0` at
    /// every binder, so it must not be fed back into the nominal substitution).
    /// If the bound is reached, exploration stops and [`Lts::is_truncated`]
    /// returns `true`; transitions into states that were never created are
    /// omitted.
    pub fn explore(start: &Proc, max_states: usize) -> Lts {
        let mut states: Vec<Proc> = Vec::new();
        let mut index: HashMap<Proc, usize> = HashMap::new();
        let mut transitions: Vec<Vec<Transition>> = Vec::new();
        let mut truncated = false;
        let mut queue: VecDeque<(usize, Proc)> = VecDeque::new();

        let start_canon = canonicalize(start);
        index.insert(start_canon.clone(), 0);
        states.push(start_canon);
        transitions.push(Vec::new());
        queue.push_back((0, start.clone()));

        while let Some((from, rep)) = queue.pop_front() {
            for step in step_labeled(&rep) {
                let key = canonicalize(&step.reduct);
                let target = if let Some(&t) = index.get(&key) {
                    t
                } else if states.len() >= max_states {
                    truncated = true;
                    continue;
                } else {
                    let t = states.len();
                    index.insert(key.clone(), t);
                    states.push(key);
                    transitions.push(Vec::new());
                    queue.push_back((t, step.reduct));
                    t
                };
                transitions[from].push(Transition {
                    label: step.channel,
                    message: step.message,
                    target,
                });
            }
        }

        Lts {
            states,
            index,
            transitions,
            truncated,
        }
    }

    /// The initial state's index (always `0`).
    pub fn initial(&self) -> usize {
        0
    }

    /// The number of distinct states.
    pub fn num_states(&self) -> usize {
        self.states.len()
    }

    /// The total number of transitions.
    pub fn num_transitions(&self) -> usize {
        self.transitions.iter().map(Vec::len).sum()
    }

    /// The canonical process at state `i`.
    pub fn state(&self, i: usize) -> &Proc {
        &self.states[i]
    }

    /// The index of a process's canonical form, if it is a state of this LTS.
    pub fn state_index(&self, p: &Proc) -> Option<usize> {
        self.index.get(&canonicalize(p)).copied()
    }

    /// The outgoing transitions of state `i`.
    pub fn transitions(&self, i: usize) -> &[Transition] {
        &self.transitions[i]
    }

    /// Whether state `i` has no outgoing transitions (a deadlock / normal form).
    pub fn is_terminal(&self, i: usize) -> bool {
        self.transitions[i].is_empty()
    }

    /// Whether exploration hit the `max_states` bound (so the LTS is a fragment
    /// of a larger, possibly infinite, state space).
    pub fn is_truncated(&self) -> bool {
        self.truncated
    }

    /// Render the LTS as Graphviz DOT for inspection.
    pub fn to_dot(&self) -> String {
        let mut out = String::from("digraph lts {\n  rankdir=LR;\n");
        for (i, s) in self.states.iter().enumerate() {
            let shape = if i == 0 { "doublecircle" } else { "circle" };
            out.push_str(&format!(
                "  n{i} [shape={shape},label=\"{i}: {}\"];\n",
                escape(&format_proc(s)),
            ));
        }
        for (from, edges) in self.transitions.iter().enumerate() {
            for t in edges {
                out.push_str(&format!(
                    "  n{from} -> n{} [label=\"{}\"];\n",
                    t.target,
                    escape(&format_edge(&t.label, &t.message)),
                ));
            }
        }
        out.push_str("}\n");
        out
    }
}

// ===========================================================================
// Partial-order reduction (POR) — an opt-in, reduced explorer.
// ===========================================================================

impl Lts {
    /// Explore the reduction graph from `start` under **partial-order reduction**
    /// (the ample-set method), producing a *reduced* [`Lts`] that collapses
    /// redundant interleavings of independent `Comm` steps.
    ///
    /// `observed` is the set of channels an observer may watch (as in
    /// `stratum_equiv`'s N-barbed observation set): a step is *visible* if it
    /// changes the set of top-level output barbs on those channels. POR only ever
    /// defers *invisible*, *independent* steps.
    ///
    /// # What this preserves — and what it does NOT
    ///
    /// Classic ample-set POR preserves exactly the **stutter-invariant**
    /// properties over the observed labelling. Concretely, the reduced LTS this
    /// returns preserves:
    ///
    /// * **reachability / safety of barb-observations on the `observed`
    ///   channels** — the set of barb-valuations (which observed channels carry a
    ///   top-level output) reachable from the initial state is identical to that
    ///   of the full [`Lts::explore`]; hence non-next μ-calculus verdicts phrased
    ///   over those barb propositions (e.g. `EF`/`AG` of a barb predicate) agree.
    ///
    /// It **does NOT** preserve, and must NOT be used for:
    ///
    /// * **bisimulation** — `stratum_equiv` computes barbed bisimulation over
    ///   the *full* branching structure; POR deliberately drops branches, so a
    ///   POR LTS can be non-bisimilar to the full one. Always use
    ///   [`Lts::explore`] there.
    /// * **next-time modalities** — `⟨a⟩`/`[a]` (single-step `Diamond`/`Box`)
    ///   reference individual transitions, which POR reorders and elides.
    ///   Verdicts for next-time formulas must use [`Lts::explore`].
    ///
    /// [`Lts::explore`] is left byte-for-byte behaviourally unchanged; this is a
    /// wholly separate entry point.
    ///
    /// # Provisos enforced
    ///
    /// The ample set `ample(s) ⊆ enabled(s)` is chosen to satisfy:
    ///
    /// * **C0** — `ample(s)` is nonempty iff `enabled(s)` is.
    /// * **C1 (persistence)** — realized *soundly and conservatively*. When
    ///   `enabled(s)` has more than one step, `ample(s)` may be a **singleton**
    ///   `{α}` only when α is invisible, *independent* of every
    ///   other enabled step (disjoint parallel components *and* a distinct firing
    ///   channel), and **future-stable**: no *other* top-level component can ever
    ///   present a communication on α's channel `c`, over-approximated by
    ///   requiring that no other component (a) contains a bound variable in any
    ///   channel position (so no substitution can *synthesize* a `c`-channel) nor
    ///   (b) mentions `c` as a channel anywhere (so no `c`-partner can *surface*
    ///   from under a prefix or quote). Under those conditions `{α}` is a genuine
    ///   persistent set. If no such step exists, `ample(s) = enabled(s)` (a full
    ///   expansion, trivially persistent) — correctness first, reduction second.
    /// * **C2 (visibility)** — a singleton `ample(s) ≠ enabled(s)` never contains
    ///   a visible step.
    /// * **C3 (cycle / ignoring)** — a DFS stack proviso: a singleton whose
    ///   successor is already on the current search stack is rejected, forcing a
    ///   full expansion. Every cycle therefore contains at least one fully
    ///   expanded state, so no enabled step is deferred forever.
    ///
    /// Like [`Lts::explore`], exploration is bounded by `max_states`;
    /// [`Lts::is_truncated`] reports whether the bound was hit.
    pub fn explore_por(start: &Proc, max_states: usize, observed: &[Name]) -> Lts {
        let mut b = PorBuilder {
            states: Vec::new(),
            index: HashMap::new(),
            transitions: Vec::new(),
            on_stack: Vec::new(),
            truncated: false,
        };
        let start_canon = canonicalize(start);
        b.index.insert(start_canon.clone(), 0);
        b.states.push(start_canon);
        b.transitions.push(Vec::new());
        b.on_stack.push(false);
        b.dfs(0, start.clone(), observed, max_states);

        Lts {
            states: b.states,
            index: b.index,
            transitions: b.transitions,
            truncated: b.truncated,
        }
    }
}

/// One enabled `Comm` transition of a state, enriched with the data POR needs:
/// the parallel-component occurrences it consumes, and whether it is visible.
struct Enabled {
    /// `≡N`-canonical firing channel (as in [`Transition::label`]).
    channel: Name,
    /// `≡N`-canonical transmitted message (as in [`Transition::message`]).
    message: Name,
    /// Nominal successor, so it can be stepped again.
    reduct: Proc,
    /// Canonical successor — the dedup / target key.
    target: Proc,
    /// The indices (into the flattened components) this redex consumes. After
    /// dedup this is the *union* over every redex that produced this transition,
    /// which is conservative (more components ⇒ more likely judged dependent).
    comps: BTreeSet<usize>,
    /// Whether firing changes the observed-barb valuation.
    visible: bool,
}

/// Mutable state threaded through the POR depth-first search.
struct PorBuilder {
    states: Vec<Proc>,
    index: HashMap<Proc, usize>,
    transitions: Vec<Vec<Transition>>,
    on_stack: Vec<bool>,
    truncated: bool,
}

impl PorBuilder {
    fn dfs(&mut self, from: usize, rep: Proc, observed: &[Name], max_states: usize) {
        self.on_stack[from] = true;
        let (enabled, comps) = enabled_transitions(&rep, observed);
        let ample = self.choose_ample(&enabled, &comps);

        for k in ample {
            let channel = enabled[k].channel.clone();
            let message = enabled[k].message.clone();
            let target = enabled[k].target.clone();
            let reduct = enabled[k].reduct.clone();

            let target_idx = if let Some(&idx) = self.index.get(&target) {
                idx
            } else if self.states.len() >= max_states {
                self.truncated = true;
                continue;
            } else {
                let idx = self.states.len();
                self.index.insert(target.clone(), idx);
                self.states.push(target);
                self.transitions.push(Vec::new());
                self.on_stack.push(false);
                self.dfs(idx, reduct, observed, max_states);
                idx
            };
            self.transitions[from].push(Transition {
                label: channel,
                message,
                target: target_idx,
            });
        }

        self.on_stack[from] = false;
    }

    /// Pick the ample set as a list of indices into `enabled` (see the provisos
    /// documented on [`Lts::explore_por`]).
    fn choose_ample(&self, enabled: &[Enabled], comps: &[Proc]) -> Vec<usize> {
        if enabled.is_empty() {
            return Vec::new(); // C0: terminal.
        }
        if enabled.len() > 1 {
            for (k, t) in enabled.iter().enumerate() {
                if t.visible {
                    continue; // C2.
                }
                if !independent_of_others(k, enabled) {
                    continue; // C1: not independent of all other enabled steps.
                }
                if !future_stable(comps, t) {
                    continue; // C1: a c-partner could arise on a non-α path.
                }
                if let Some(&idx) = self.index.get(&t.target) {
                    if self.on_stack[idx] {
                        continue; // C3: would close a cycle, deferring the rest.
                    }
                }
                return vec![k];
            }
        }
        (0..enabled.len()).collect() // full expansion.
    }
}

/// Whether transition `k` is independent of every other enabled transition:
/// disjoint parallel components *and* a distinct (`≢N`) firing channel. This is
/// a conservative over-approximation of dependence — uncertain pairs are treated
/// as dependent, which only ever reduces the reduction, never its soundness.
fn independent_of_others(k: usize, enabled: &[Enabled]) -> bool {
    let a = &enabled[k];
    enabled
        .iter()
        .enumerate()
        .all(|(m, b)| m == k || (a.channel != b.channel && a.comps.is_disjoint(&b.comps)))
}

/// Whether deferring `t` is safe: no *other* top-level component can ever present
/// a communication on `t`'s channel `c`, so `{t}` stays a persistent set along
/// every non-`t` path. Conservative: a component blocks deferral if it has any
/// variable in a channel position (a substitution could synthesize `c`) or
/// mentions `c` as a channel anywhere (a `c`-partner could surface from under a
/// prefix or a quote). Deliberately over-conservative: a variable-channel or a
/// `c`-mention buried *inside a quote* is impervious to substitution and can
/// never fire, yet still blocks deferral here — safe (it only forgoes some
/// reduction), and not required for correctness.
fn future_stable(comps: &[Proc], t: &Enabled) -> bool {
    comps.iter().enumerate().all(|(k, comp)| {
        t.comps.contains(&k) || (!has_var_channel(comp) && !mentions_channel(comp, &t.channel))
    })
}

/// All enabled `Comm` transitions of the nominal representative `rep`, together
/// with its flattened active components. Mirrors `stratum_core`'s redex
/// enumeration (default `≡N` synchronization) but records component occurrences
/// and visibility; transitions are deduplicated on `(channel, message, target)`
/// exactly as [`step_labeled`], unioning component sets on collision.
fn enabled_transitions(rep: &Proc, observed: &[Name]) -> (Vec<Enabled>, Vec<Proc>) {
    let mut comps = Vec::new();
    flatten(rep, &mut comps);
    let src_barbs = observed_barbs(&comps, observed);

    let mut list: Vec<Enabled> = Vec::new();
    let mut seen: HashMap<(Name, Name, Proc), usize> = HashMap::new();

    for i in 0..comps.len() {
        let Proc::Lift { chan: x0, arg: q } = &comps[i] else {
            continue;
        };
        for j in 0..comps.len() {
            if i == j {
                continue;
            }
            let Proc::Input {
                chan: x1,
                bound,
                body,
            } = &comps[j]
            else {
                continue;
            };
            if !name_equiv(x0, x1) {
                continue;
            }

            let message = Name::Quote(q.clone());
            let reduced = subst_semantic(body, *bound, &message);
            let mut rest: Vec<Proc> = comps
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != i && *k != j)
                .map(|(_, c)| c.clone())
                .collect();
            rest.push(reduced);
            let reduct = Proc::Par(rest);

            let channel = canonicalize_name(x0);
            let message = canonicalize_name(&message);
            let target = canonicalize(&reduct);
            let key = (channel.clone(), message.clone(), target.clone());

            if let Some(&e) = seen.get(&key) {
                list[e].comps.insert(i);
                list[e].comps.insert(j);
            } else {
                let mut tcomps = Vec::new();
                flatten(&target, &mut tcomps);
                let visible = observed_barbs(&tcomps, observed) != src_barbs;
                let mut cset = BTreeSet::new();
                cset.insert(i);
                cset.insert(j);
                seen.insert(key, list.len());
                list.push(Enabled {
                    channel,
                    message,
                    reduct,
                    target,
                    comps: cset,
                    visible,
                });
            }
        }
    }

    (list, comps)
}

/// Flatten `p` into its active parallel components (dropping units `0`, splicing
/// nested parallels), without descending under any prefix — the same active-
/// component notion `stratum_core` reduces over.
pub(crate) fn flatten(p: &Proc, out: &mut Vec<Proc>) {
    match p {
        Proc::Zero => {}
        Proc::Par(ps) => {
            for q in ps {
                flatten(q, out);
            }
        }
        other => out.push(other.clone()),
    }
}

/// The canonical channels on which `comps` carry a top-level output `≡N` an
/// observed name — the observed-barb valuation (cf. `stratum_equiv::strong_barbs`).
fn observed_barbs(comps: &[Proc], observed: &[Name]) -> BTreeSet<Name> {
    let mut set = BTreeSet::new();
    for c in comps {
        if let Proc::Lift { chan, .. } = c {
            if observed.iter().any(|n| name_equiv(chan, n)) {
                set.insert(canonicalize_name(chan));
            }
        }
    }
    set
}

/// Whether any `Lift`/`Input` node anywhere in `p` (including inside lifted
/// arguments, input bodies, drops, and *quoted* processes) uses a bound variable
/// in its channel position. Deliberately over-conservative: a variable channel
/// frozen under a quote (`⌜…y(z)…⌝`) is impervious to substitution (§2.6) and can
/// never fire, but is still flagged — safe, forgoing some reduction, not needed
/// for correctness.
fn has_var_channel(p: &Proc) -> bool {
    match p {
        Proc::Zero => false,
        Proc::Drop(n) => name_has_var_channel(n),
        Proc::Lift { chan, arg } => {
            matches!(chan, Name::Var(_)) || name_has_var_channel(chan) || has_var_channel(arg)
        }
        Proc::Input { chan, body, .. } => {
            matches!(chan, Name::Var(_)) || name_has_var_channel(chan) || has_var_channel(body)
        }
        Proc::Par(ps) => ps.iter().any(has_var_channel),
    }
}

fn name_has_var_channel(n: &Name) -> bool {
    match n {
        Name::Var(_) => false,
        Name::Quote(p) => has_var_channel(p),
    }
}

/// Whether any `Lift`/`Input` node anywhere in `p` (including inside lifted
/// arguments, input bodies, drops, and *quoted* processes) uses a channel `≡N c`.
fn mentions_channel(p: &Proc, c: &Name) -> bool {
    match p {
        Proc::Zero => false,
        Proc::Drop(n) => name_mentions_channel(n, c),
        Proc::Lift { chan, arg } => {
            name_equiv(chan, c) || name_mentions_channel(chan, c) || mentions_channel(arg, c)
        }
        Proc::Input { chan, body, .. } => {
            name_equiv(chan, c) || name_mentions_channel(chan, c) || mentions_channel(body, c)
        }
        Proc::Par(ps) => ps.iter().any(|q| mentions_channel(q, c)),
    }
}

fn name_mentions_channel(n: &Name, c: &Name) -> bool {
    match n {
        Name::Var(_) => false,
        Name::Quote(p) => mentions_channel(p, c),
    }
}

// ===========================================================================
// Symmetry reduction — an opt-in, quotiented explorer.
// ===========================================================================

impl Lts {
    /// Explore the reduction graph from `start` under **symmetry reduction**,
    /// quotienting the state space by the symmetric group that permutes a set of
    /// **interchangeable channels**.
    ///
    /// Many protocols are built from interchangeable agents (N identical clients,
    /// a pool of equivalent workers, …). Their state spaces then contain large
    /// families of states that differ only by *which* agent is in *which* role —
    /// states related by a permutation of the agents' channels. This explorer
    /// collapses each such family to a single node.
    ///
    /// `interchangeable` is the generating set `S = {c₀, …, c_{k-1}}` of channels
    /// the caller declares mutually exchangeable; the symmetry group is the full
    /// **symmetric group `Sym(S)`** permuting them. Two states are identified when
    /// one is carried to the other by some `π ∈ Sym(S)` (permuting those channels
    /// throughout the term — in the channel positions of `Lift`/`Input`, in
    /// `Drop`s, and *inside quotes and messages*, matched up to `≡N`). Each state
    /// is keyed by its **canonical orbit representative**: the `≡`-canonical
    /// minimum (under `Proc`'s `Ord`) over the `|S|!` images `π(state)`.
    ///
    /// # Precondition — a genuine symmetry (enforced by fallback)
    ///
    /// The caller must supply a set for which permuting the channels is a genuine
    /// **system automorphism**. The sufficient, checked condition is that the set
    /// is an **independent generator**: *no interchangeable channel occurs (up to
    /// `≡N`) inside another's quoted body* (e.g. `c₀ = ⌜0⌝`, `c₁ = ⌜c₀⟨|0|⟩⌝`
    /// **violates** this — `c₀` is buried in `c₁`). Under this condition the channel
    /// permutation is a `≡N`-automorphism, so the quotient is sound.
    ///
    /// When the condition **fails**, permuting a channel would not permute its
    /// buried occurrences, so distinct states could be wrongly conflated and
    /// reachable behaviour dropped. To stay sound on *every* input, this method
    /// then **conservatively falls back to the full [`Lts::explore`]** — it
    /// produces a reduced LTS only when the declared symmetry is *provably*
    /// independent, and an exact, unquotiented one otherwise. The check is
    /// conservative: any doubtful occurrence is treated as a dependence.
    ///
    /// # Intended scale
    ///
    /// The representative is computed by enumerating all `|S|!` permutations of
    /// the interchangeable set and canonicalizing each image, so this is intended
    /// for **small** interchangeable sets (the usual case: a handful of symmetric
    /// agents). The per-state cost is `Θ(|S|! · |state|)`; it is deliberately
    /// transparent rather than clever.
    ///
    /// # What this preserves — and what it does NOT
    ///
    /// **Provided the genuine-symmetry precondition above holds** (otherwise the
    /// result *is* the full [`Lts::explore`], which preserves everything), the
    /// quotient LTS is bisimilar to the full [`Lts::explore`] for exactly the
    /// **symmetry-invariant** properties — those whose truth is unchanged by
    /// permuting the interchangeable channels. Concretely it preserves:
    ///
    /// * **reachability / safety of symmetric predicates** — e.g. "some agent
    ///   reaches `done`", the number of concurrent barbs on a *non*-interchangeable
    ///   channel, or "some interchangeable channel carries a barb". The set of
    ///   reachable symmetry-invariant valuations is identical to the full LTS, so
    ///   non-next μ-calculus verdicts (`EF`/`AG`, …) over symmetric barb
    ///   propositions agree.
    ///
    /// It **does NOT** preserve, and must NOT be used for:
    ///
    /// * **properties naming a specific interchangeable channel asymmetrically** —
    ///   e.g. "`c₃` (rather than some cᵢ) carries a barb". The quotient conflates
    ///   `c₃` with its orbit, so such a predicate is not well-defined on it. Phrase
    ///   observations over the *whole* interchangeable set (or over fixed,
    ///   non-interchangeable channels) instead.
    /// * **bisimulation over asymmetric observations** and **next-time modalities**
    ///   that reference a specific interchangeable channel — use [`Lts::explore`].
    ///
    /// Because states are stepped through their orbit representative, the
    /// firing-channel **label** and **message** of a lifted transition are recorded
    /// *in the representative's frame*: they are only meaningful **up to the
    /// group**. Symmetry-invariant label reasoning (a barb on *some* cᵢ, or on a
    /// fixed non-interchangeable channel) is stable; the specific interchangeable
    /// identity of a label is not.
    ///
    /// With an **empty** `interchangeable` set the group is trivial and this
    /// coincides exactly with [`Lts::explore`] (no quotient). [`Lts::explore`] is
    /// left byte-for-byte behaviourally unchanged; this is a wholly separate entry
    /// point.
    ///
    /// Like [`Lts::explore`], exploration is bounded by `max_states`;
    /// [`Lts::is_truncated`] reports whether the bound was hit.
    pub fn explore_symmetric(start: &Proc, max_states: usize, interchangeable: &[Name]) -> Lts {
        // Canonicalize the generating set once, so `≡N` matching and the
        // substituted images are stable and re-matchable across compositions. A
        // `canonical name → index` map lets `permute_name` match a channel with a
        // single canonicalization + lookup instead of an `≡N` scan of the set.
        let inter: Vec<Name> = interchangeable.iter().map(canonicalize_name).collect();

        // Soundness guard. The match-wins channel permutation (`permute_name`) is a
        // `≡N`-automorphism — hence the quotient is sound — only when the declared
        // channels are a **genuine independent generator**: no interchangeable
        // channel occurs (up to `≡N`) inside another's quoted body. If that fails,
        // permuting a channel would fail to also permute its buried occurrences,
        // conflating genuinely distinct states and *dropping reachable behaviour*.
        // Rather than emit unsound verdicts we conservatively fall back to the full,
        // unquotiented [`Lts::explore`], which is always correct.
        if !interchange_is_independent(&inter) {
            return Lts::explore(start, max_states);
        }

        let sym = Symmetry {
            index: inter
                .iter()
                .enumerate()
                .map(|(i, n)| (n.clone(), i))
                .collect(),
            names: inter,
        };
        let perms = all_permutations(sym.names.len());

        let mut states: Vec<Proc> = Vec::new();
        let mut index: HashMap<Proc, usize> = HashMap::new();
        let mut transitions: Vec<Vec<Transition>> = Vec::new();
        let mut truncated = false;
        // Each queue entry carries a *nominal* representative of the orbit (so it
        // can be stepped without feeding a canonical de-Bruijn term back into the
        // substitution engine); the identity key is its canonical orbit minimum.
        let mut queue: VecDeque<(usize, Proc)> = VecDeque::new();

        let (start_key, start_rep) = orbit_rep(start, &sym, &perms);
        index.insert(start_key.clone(), 0);
        states.push(start_key);
        transitions.push(Vec::new());
        queue.push_back((0, start_rep));

        while let Some((from, rep)) = queue.pop_front() {
            // Stepping the orbit representative alone suffices: ρ-reduction is
            // equivariant under the channel permutation, so every outgoing edge of
            // every orbit member is realized (up to the group) by an edge of the
            // representative, retargeted to the target's orbit representative.
            for step in step_labeled(&rep) {
                let (key, target_rep) = orbit_rep(&step.reduct, &sym, &perms);
                let target = if let Some(&t) = index.get(&key) {
                    t
                } else if states.len() >= max_states {
                    truncated = true;
                    continue;
                } else {
                    let t = states.len();
                    index.insert(key.clone(), t);
                    states.push(key);
                    transitions.push(Vec::new());
                    queue.push_back((t, target_rep));
                    t
                };
                transitions[from].push(Transition {
                    label: step.channel,
                    message: step.message,
                    target,
                });
            }
        }

        Lts {
            states,
            index,
            transitions,
            truncated,
        }
    }
}

/// The interchangeable channel set, in canonical form, with an index for fast
/// `≡N` matching. `names[i]` is the `i`-th interchangeable channel (`≡N`-canonical)
/// and `index` maps that canonical name back to `i`.
struct Symmetry {
    names: Vec<Name>,
    index: HashMap<Name, usize>,
}

/// Whether the (canonical) interchangeable set is a **genuine independent
/// generator**: no channel occurs (up to `≡N`) strictly *inside* another's quoted
/// body. This is the sufficient condition under which the match-wins channel
/// permutation is a `≡N`-automorphism, so the symmetry quotient is sound; when it
/// fails, [`Lts::explore_symmetric`] falls back to full exploration.
///
/// Conservative by construction: an occurrence anywhere — in a channel position,
/// a `Drop`, a lifted payload, or nested inside a further quote — counts as a
/// dependence (self-containment is impossible, since quote depth strictly
/// decreases under a quote, so only distinct pairs are checked).
fn interchange_is_independent(inter: &[Name]) -> bool {
    for (i, ci) in inter.iter().enumerate() {
        for (j, cj) in inter.iter().enumerate() {
            if i != j && name_body_contains(cj, ci) {
                return false; // ci occurs inside cj's body — not independent.
            }
        }
    }
    true
}

/// Whether `needle` (`≡N`-canonical) occurs up to `≡N` strictly *inside*
/// `container`'s quoted body (below the top-level name itself).
fn name_body_contains(container: &Name, needle: &Name) -> bool {
    match container {
        Name::Var(_) => false,
        Name::Quote(p) => proc_contains_name(p, needle),
    }
}

/// Whether `needle` occurs up to `≡N` as any sub-name anywhere in `p` — channel
/// positions, `Drop`s, lifted payloads, input bodies, and inside nested quotes.
fn proc_contains_name(p: &Proc, needle: &Name) -> bool {
    match p {
        Proc::Zero => false,
        Proc::Drop(n) => name_contains_name(n, needle),
        Proc::Lift { chan, arg } => {
            name_contains_name(chan, needle) || proc_contains_name(arg, needle)
        }
        Proc::Input { chan, body, .. } => {
            name_contains_name(chan, needle) || proc_contains_name(body, needle)
        }
        Proc::Par(ps) => ps.iter().any(|q| proc_contains_name(q, needle)),
    }
}

/// Whether the name `n` is `≡N needle`, or `needle` occurs inside `n`'s quote.
fn name_contains_name(n: &Name, needle: &Name) -> bool {
    name_equiv(n, needle)
        || match n {
            Name::Var(_) => false,
            Name::Quote(p) => proc_contains_name(p, needle),
        }
}

/// The canonical orbit representative of `nominal` under `Sym(sym.names)`,
/// together with a *nominal* term that canonicalizes to it (the image achieving
/// the minimum), suitable for further stepping.
///
/// Enumerates every permutation `π` in `perms`, renames the interchangeable
/// channels of `nominal` accordingly (keeping binder symbols intact, so the image
/// stays a steppable nominal term), canonicalizes, and keeps the `≡`-least image.
/// Ties on the canonical key are broken by first occurrence, which is
/// deterministic and irrelevant to the key. Because `perms` always contains the
/// identity, the result is well-defined (and for an empty set it is exactly
/// `(canonicalize(nominal), nominal.clone())`).
fn orbit_rep(nominal: &Proc, sym: &Symmetry, perms: &[Vec<usize>]) -> (Proc, Proc) {
    let mut best: Option<(Proc, Proc)> = None;
    for perm in perms {
        let image = permute_proc(nominal, sym, perm);
        let key = canonicalize(&image);
        match &best {
            Some((best_key, _)) if *best_key <= key => {}
            _ => best = Some((key, image)),
        }
    }
    best.expect("perms always contains the identity permutation")
}

/// Rename the interchangeable channels of `p` by `perm`, throughout the term.
///
/// Binder symbols and non-interchangeable names are preserved verbatim, so the
/// result is a well-formed nominal term with the same reduction structure up to
/// the renaming (ρ-reduction is equivariant under this map).
fn permute_proc(p: &Proc, sym: &Symmetry, perm: &[usize]) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => Proc::Drop(permute_name(n, sym, perm)),
        Proc::Lift { chan, arg } => Proc::Lift {
            chan: permute_name(chan, sym, perm),
            arg: Box::new(permute_proc(arg, sym, perm)),
        },
        Proc::Input { chan, bound, body } => Proc::Input {
            chan: permute_name(chan, sym, perm),
            bound: *bound,
            body: Box::new(permute_proc(body, sym, perm)),
        },
        Proc::Par(ps) => Proc::Par(ps.iter().map(|q| permute_proc(q, sym, perm)).collect()),
    }
}

/// Rename `n` by `perm`: if `n ≡N cᵢ` for an interchangeable `cᵢ`, replace the
/// whole name with the canonical `c_{π(i)}`; otherwise recurse under the quote so
/// interchangeable channels *nested inside* a name are permuted too.
fn permute_name(n: &Name, sym: &Symmetry, perm: &[usize]) -> Name {
    if !sym.names.is_empty() {
        if let Some(&i) = sym.index.get(&canonicalize_name(n)) {
            return sym.names[perm[i]].clone();
        }
    }
    match n {
        Name::Var(_) => n.clone(),
        Name::Quote(p) => Name::Quote(Box::new(permute_proc(p, sym, perm))),
    }
}

/// All permutations of `0..n` (as index vectors). `n = 0` yields the single empty
/// permutation `[[]]`. Intended for small `n` (the interchangeable-set size).
fn all_permutations(n: usize) -> Vec<Vec<usize>> {
    let mut current: Vec<usize> = (0..n).collect();
    let mut out = Vec::new();
    heap_permute(&mut current, n, &mut out);
    out
}

/// Heap's algorithm: emit every permutation of `current[..k]`'s ordering.
fn heap_permute(current: &mut [usize], k: usize, out: &mut Vec<Vec<usize>>) {
    if k <= 1 {
        out.push(current.to_vec());
        return;
    }
    for i in 0..k {
        heap_permute(current, k - 1, out);
        if k.is_multiple_of(2) {
            current.swap(i, k - 1);
        } else {
            current.swap(0, k - 1);
        }
    }
}

pub(crate) fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// A compact edge rendering `channel⟨message⟩`: the firing channel together with
/// the transmitted payload, kept readable by [`format_name`]'s compact quote
/// notation (e.g. `@0⟨@0⟩`).
fn format_edge(channel: &Name, message: &Name) -> String {
    format!("{}⟨{}⟩", format_name(channel), format_name(message))
}

/// A compact surface rendering of a process for inspection/labels.
pub fn format_proc(p: &Proc) -> String {
    match p {
        Proc::Zero => "0".to_string(),
        Proc::Drop(n) => format!("*{}", format_name(n)),
        Proc::Lift { chan, arg } => format!("{}!({})", format_name(chan), format_proc(arg)),
        Proc::Input { chan, body, .. } => format!("{}(_).{}", format_name(chan), format_proc(body)),
        Proc::Par(ps) => {
            if ps.is_empty() {
                "0".to_string()
            } else {
                ps.iter().map(format_proc).collect::<Vec<_>>().join(" | ")
            }
        }
    }
}

/// A compact surface rendering of a name.
pub fn format_name(n: &Name) -> String {
    match n {
        Name::Var(i) => format!("v{i}"),
        Name::Quote(p) => match p.as_ref() {
            Proc::Zero => "@0".to_string(),
            other => format!("@({})", format_proc(other)),
        },
    }
}
