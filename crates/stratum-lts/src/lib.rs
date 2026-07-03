//! # stratum-lts
//!
//! The **trace grain** (ρ) of the πρσϕ-Formalism: a labelled transition system
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
fn flatten(p: &Proc, out: &mut Vec<Proc>) {
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

fn escape(s: &str) -> String {
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
