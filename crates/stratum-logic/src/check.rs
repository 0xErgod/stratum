//! The model-checking algorithm: denotational μ-calculus semantics over an
//! [`Lts`], computed by fixpoint iteration on finite state sets, extended with
//! epistemic operators over agents' information fields.
//!
//! The denotation of a formula is the set of states satisfying it, represented
//! as a bit vector indexed by state. Because formulas are in positive normal
//! form, each fixpoint body is a monotone map on the finite powerset lattice, so
//! Kleene iteration from `∅` (for `μ`) or from all states (for `ν`) converges.
//! `Knows`/`Possible` are monotone too, so they compose freely with fixpoints.
//!
//! Epistemic operators need each agent's information field (a [`Field`], a
//! partition of the states). These are supplied as a map from agent name to
//! field; see [`check_epistemic`]. The plain [`check`] uses an empty map, under
//! which an undeclared agent is treated as omniscient (its field is discrete, so
//! `K_A φ ≡ φ`).
//!
//! Fairness follows the same "supplied by the caller" design. Liveness (`AF`)
//! over a concurrent system is only meaningful under a **fairness assumption**:
//! the plain `af` counts an infinite run that forever starves an enabled action
//! as a genuine counterexample, even when no real scheduler would. A [`Fairness`]
//! condition is a *generalized-Büchi* set of constraints — each a state
//! predicate (a [`Formula`]) that a *fair* infinite run must satisfy infinitely
//! often. The fair operators [`Formula::FairEg`]/[`Formula::FairAf`] are then
//! decided against that condition by [`check_fair`]/[`holds_fair`]. The core
//! primitive is `fair_eg` — the set of states from which a fair path exists —
//! computed by the standard Emerson–Lei nested fixpoint (see [`fair_eg_set`]);
//! `fair_af(φ) = ¬ fair_eg(¬φ)`. Deadlocks are handled exactly as `eg`/`af`
//! handle them: a fair path is infinite, so the fixpoint's `EX`-progress conjunct
//! excludes terminal states with no successors.

use std::collections::{HashMap, VecDeque};

use stratum_core::{Name, Proc};
use stratum_field::Field;
use stratum_lts::Lts;

use crate::formula::Formula;

/// A set of states as a bit vector indexed by state number.
type StateSet = Vec<bool>;

/// Per-agent information fields, keyed by agent name.
pub type Agents = HashMap<String, Field>;

/// A **fairness condition** as a generalized-Büchi set of constraints.
///
/// Each constraint is a state predicate expressed as a [`Formula`], in exactly
/// the same vocabulary (atomic propositions, modalities, fixpoints, …) as every
/// other property — chosen over a raw bit vector or an opaque `Fn(&Proc)->bool`
/// so that fairness assumptions read like the rest of the logic, compose with
/// the labelling, and are decided by the same `eval`. A fixed constraint set is
/// a `Formula` list because constraints are *state* sets, not paths.
///
/// A run is **fair** iff it is infinite and, for every constraint `C`, it enters
/// the set of states satisfying `C` infinitely often. Liveness verdicts under
/// this condition are given by [`Formula::FairEg`]/[`Formula::FairAf`], decided
/// by [`check_fair`]. With no constraints, every infinite run is fair, so
/// `fair_eg`/`fair_af` coincide with `eg`/`af`-without-deadlock-vacuity (see
/// [`fair_eg_set`]).
///
/// Mirrors the [`Agents`] pattern: caller-supplied data threaded into the
/// checker, empty by default.
#[derive(Clone, Debug, Default)]
pub struct Fairness {
    constraints: Vec<Formula>,
}

impl Fairness {
    /// The empty fairness condition (no constraints): every infinite run is fair.
    pub fn new() -> Self {
        Fairness {
            constraints: Vec::new(),
        }
    }

    /// Add a fairness constraint — a state predicate that a fair run must satisfy
    /// infinitely often — returning `self` for chaining.
    #[must_use]
    pub fn constrain(mut self, constraint: Formula) -> Self {
        self.constraints.push(constraint);
        self
    }

    /// Build a fairness condition from an iterator of constraint predicates.
    pub fn from_constraints(constraints: impl IntoIterator<Item = Formula>) -> Self {
        Fairness {
            constraints: constraints.into_iter().collect(),
        }
    }

    /// The constraint predicates of this condition.
    pub fn constraints(&self) -> &[Formula] {
        &self.constraints
    }
}

fn full(n: usize) -> StateSet {
    vec![true; n]
}
fn empty(n: usize) -> StateSet {
    vec![false; n]
}

#[allow(clippy::too_many_arguments)]
fn eval<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    f: &Formula,
    env: &mut HashMap<String, StateSet>,
    label: &L,
    agents: &Agents,
    fairness: &Fairness,
) -> StateSet {
    let n = lts.num_states();
    match f {
        Formula::True => full(n),
        Formula::False => empty(n),
        Formula::Prop(p) => (0..n).map(|i| label(p, lts.state(i))).collect(),
        Formula::NotProp(p) => (0..n).map(|i| !label(p, lts.state(i))).collect(),
        Formula::And(a, b) => {
            let sa = eval(lts, a, env, label, agents, fairness);
            let sb = eval(lts, b, env, label, agents, fairness);
            (0..n).map(|i| sa[i] && sb[i]).collect()
        }
        Formula::Or(a, b) => {
            let sa = eval(lts, a, env, label, agents, fairness);
            let sb = eval(lts, b, env, label, agents, fairness);
            (0..n).map(|i| sa[i] || sb[i]).collect()
        }
        Formula::Diamond(act, g) => {
            let sg = eval(lts, g, env, label, agents, fairness);
            (0..n)
                .map(|i| {
                    lts.transitions(i)
                        .iter()
                        .any(|t| act.matches(&t.label) && sg[t.target])
                })
                .collect()
        }
        Formula::Box(act, g) => {
            let sg = eval(lts, g, env, label, agents, fairness);
            (0..n)
                .map(|i| {
                    lts.transitions(i)
                        .iter()
                        .all(|t| !act.matches(&t.label) || sg[t.target])
                })
                .collect()
        }
        Formula::Var(x) => env.get(x).cloned().unwrap_or_else(|| empty(n)),
        Formula::Mu(x, g) => fixpoint(lts, x, g, env, label, agents, fairness, empty(n)),
        Formula::Nu(x, g) => fixpoint(lts, x, g, env, label, agents, fairness, full(n)),
        Formula::Knows(agent, g) => {
            let sg = eval(lts, g, env, label, agents, fairness);
            epistemic(lts, agent, agents, &sg, Quant::All)
        }
        Formula::Possible(agent, g) => {
            let sg = eval(lts, g, env, label, agents, fairness);
            epistemic(lts, agent, agents, &sg, Quant::Any)
        }
        Formula::FairEg(g) => {
            let sg = eval(lts, g, env, label, agents, fairness);
            let cons = constraint_sets(lts, label, agents, fairness);
            fair_eg_set(lts, &sg, &cons)
        }
        Formula::FairAf(g) => {
            // fairAF φ = ¬ fairEG(¬φ): no fair path stays in ¬φ forever. Computed
            // at the set level so no formula-level negation of `g` is needed.
            let sg = eval(lts, g, env, label, agents, fairness);
            let not_phi: StateSet = sg.iter().map(|&b| !b).collect();
            let cons = constraint_sets(lts, label, agents, fairness);
            let feg = fair_eg_set(lts, &not_phi, &cons);
            feg.iter().map(|&b| !b).collect()
        }
    }
}

/// Evaluate each fairness constraint to its state set. Constraints are closed
/// state predicates, so they are evaluated in a fresh environment (they never
/// reference the surrounding fixpoint variables).
fn constraint_sets<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    label: &L,
    agents: &Agents,
    fairness: &Fairness,
) -> Vec<StateSet> {
    fairness
        .constraints
        .iter()
        .map(|c| {
            let mut cenv = HashMap::new();
            eval(lts, c, &mut cenv, label, agents, fairness)
        })
        .collect()
}

/// `EX S` — the states with some successor in `S`.
fn pre_exists(lts: &Lts, s: &StateSet) -> StateSet {
    let n = lts.num_states();
    (0..n)
        .map(|i| lts.transitions(i).iter().any(|t| s[t.target]))
        .collect()
}

/// The set of states from which some **fair path** exists that stays within
/// `phi` throughout — i.e. `fairEG φ` under the generalized-Büchi condition
/// whose constraints have state sets `constraints`.
///
/// This is the standard Emerson–Lei nested fixpoint:
///
/// ```text
/// fairEG φ = νZ. φ ∧ EX Z ∧ ⋀_i EX( E[ Z U (Z ∧ C_i) ] )
/// ```
///
/// The outer greatest fixpoint `Z` starts from `phi` and shrinks. Each iteration
/// keeps a state only if, staying inside `Z` (hence inside `φ`), it can — in at
/// least one step — reach a `C_i` state, for *every* constraint `C_i`; the inner
/// `E[Z U (Z ∧ C_i)]` is a least fixpoint computing "reaches `Z ∧ C_i` along a
/// `Z`-path". At the fixpoint every state of `Z` can revisit each `C_i`
/// arbitrarily often while remaining in `φ`, which is exactly an infinite fair
/// `φ`-path.
///
/// The `EX Z` conjunct is the implicit "visit `⊤` infinitely often" constraint:
/// it forces at least one successor inside `Z`, so a **terminal/deadlock** state
/// (no successors, hence no infinite path) is never fair — consistent with how
/// `eg`/`af` use the `⟨Any⟩⊤` conjunct. With no constraints this conjunct is all
/// that remains, so `fair_eg_set` degenerates to ordinary `EG`.
fn fair_eg_set(lts: &Lts, phi: &StateSet, constraints: &[StateSet]) -> StateSet {
    let n = lts.num_states();
    let mut z = phi.clone();
    loop {
        // Implicit ⊤ constraint: a fair path is infinite, so require a successor
        // inside Z. This is what makes deadlocks unfair.
        let pe_z = pre_exists(lts, &z);
        let mut acc: StateSet = (0..n).map(|i| z[i] && pe_z[i]).collect();

        for c in constraints {
            // target = Z ∧ C_i
            let target: StateSet = (0..n).map(|i| z[i] && c[i]).collect();
            // until = μY. target ∨ (Z ∧ EX Y): reach a target state along a Z-path.
            let mut y = target.clone();
            loop {
                let pe = pre_exists(lts, &y);
                let next: StateSet = (0..n).map(|i| target[i] || (z[i] && pe[i])).collect();
                if next == y {
                    break;
                }
                y = next;
            }
            // EX(until): make at least one step, then reach C_i staying in Z.
            let ex = pre_exists(lts, &y);
            for i in 0..n {
                acc[i] = acc[i] && ex[i];
            }
        }

        if acc == z {
            break;
        }
        z = acc;
    }
    z
}

/// Universal (`Knows`) vs existential (`Possible`) quantification over an atom.
#[derive(Clone, Copy)]
enum Quant {
    All,
    Any,
}

/// Lift a state set through an agent's information field: `Knows` keeps a state
/// iff *all* states in its atom are in `sg`; `Possible` iff *some* are. An
/// undeclared agent is omniscient (discrete field), so the set passes through.
fn epistemic(lts: &Lts, agent: &str, agents: &Agents, sg: &StateSet, quant: Quant) -> StateSet {
    let n = lts.num_states();
    let Some(field) = agents.get(agent) else {
        return sg.to_vec();
    };
    let atom_holds: Vec<bool> = field
        .atoms()
        .iter()
        .map(|members| match quant {
            Quant::All => members.iter().all(|&j| sg[j]),
            Quant::Any => members.iter().any(|&j| sg[j]),
        })
        .collect();
    (0..n).map(|i| atom_holds[field.atom_of(i)]).collect()
}

/// Kleene iteration for a fixpoint binder, starting from `init` (`∅` for `μ`,
/// all states for `ν`). Saves and restores any shadowed binding of `x`.
#[allow(clippy::too_many_arguments)]
fn fixpoint<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    x: &str,
    body: &Formula,
    env: &mut HashMap<String, StateSet>,
    label: &L,
    agents: &Agents,
    fairness: &Fairness,
    init: StateSet,
) -> StateSet {
    let saved = env.remove(x);
    let mut cur = init;
    loop {
        env.insert(x.to_string(), cur.clone());
        let next = eval(lts, body, env, label, agents, fairness);
        if next == cur {
            break;
        }
        cur = next;
    }
    env.remove(x);
    if let Some(v) = saved {
        env.insert(x.to_string(), v);
    }
    cur
}

/// The set of states satisfying `formula`, with per-agent fields for epistemic
/// operators and a fairness condition for the fair operators.
fn check_full<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    agents: &Agents,
    fairness: &Fairness,
) -> Vec<bool> {
    let mut env = HashMap::new();
    eval(lts, formula, &mut env, label, agents, fairness)
}

/// The set of states satisfying `formula`, with per-agent fields for epistemic
/// operators.
pub fn check_epistemic<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    agents: &Agents,
) -> Vec<bool> {
    check_full(lts, formula, label, agents, &Fairness::new())
}

/// The set of states satisfying `formula` under a fairness condition, used to
/// decide the fair operators [`Formula::FairEg`]/[`Formula::FairAf`]. Non-fair
/// operators behave exactly as under [`check`].
pub fn check_fair<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    fairness: &Fairness,
) -> Vec<bool> {
    check_full(lts, formula, label, &Agents::new(), fairness)
}

/// The set of states satisfying `formula` (no epistemic agents declared).
pub fn check<L: Fn(&str, &Proc) -> bool>(lts: &Lts, formula: &Formula, label: &L) -> Vec<bool> {
    check_full(lts, formula, label, &Agents::new(), &Fairness::new())
}

/// Whether state `i` satisfies `formula`.
pub fn satisfies<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    i: usize,
    formula: &Formula,
    label: &L,
) -> bool {
    check(lts, formula, label)[i]
}

/// Whether the initial state satisfies `formula`.
pub fn holds<L: Fn(&str, &Proc) -> bool>(lts: &Lts, formula: &Formula, label: &L) -> bool {
    check(lts, formula, label)[lts.initial()]
}

/// Whether the initial state satisfies `formula`, with epistemic agents.
pub fn holds_epistemic<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    agents: &Agents,
) -> bool {
    check_epistemic(lts, formula, label, agents)[lts.initial()]
}

/// Whether the initial state satisfies `formula` under a fairness condition —
/// the fairness-aware liveness verdict. A system that is live only under
/// fairness has `holds_fair(fair_af(φ), fairness)` true while plain
/// `holds(af(φ))` is false.
pub fn holds_fair<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    fairness: &Fairness,
) -> bool {
    check_fair(lts, formula, label, fairness)[lts.initial()]
}

/// A model-checking result together with whether it is *definitive*.
///
/// The μ-calculus checker runs over the bounded reachable fragment the LTS
/// explored. When the LTS was fully explored (`!Lts::is_truncated()`), the
/// reachable state space is finite and complete, so the verdict is **exact**.
/// When exploration was truncated at the state bound, the verdict is only about
/// the explored fragment (`exact == false`).
///
/// The run extractors stay sound only within their intended polarity: the *run*
/// they return is always a genuine sequence of real reductions, but its
/// endpoint's satisfaction of the queried formula is preserved under truncation
/// only for the polarity each targets — a [`witness`] for a *reachability*
/// (existential) goal, and a [`counterexample`] to a *safety* (universal)
/// invariant. For a universal `witness` goal, or a non-safety `counterexample`
/// invariant, a `Some` may be spurious under truncation, since exploration drops
/// the edges out of boundary states.
///
/// In `stratum-equiv` the analogous distinction is carried by
/// `Verdict::Inconclusive`, returned when either system's exploration truncates.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Checked {
    /// Whether the formula holds at the queried state, over the explored LTS.
    pub holds: bool,
    /// `true` if the LTS was fully explored, so `holds` is definitive; `false`
    /// if exploration was truncated, so `holds` is only about the fragment.
    pub exact: bool,
}

/// Whether the initial state satisfies `formula`, paired with whether the
/// verdict is exact (the LTS was fully explored) — see [`Checked`].
pub fn holds_checked<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
) -> Checked {
    Checked {
        holds: holds(lts, formula, label),
        exact: !lts.is_truncated(),
    }
}

/// Whether state `i` satisfies `formula`, paired with exactness — see [`Checked`].
pub fn satisfies_checked<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    i: usize,
    formula: &Formula,
    label: &L,
) -> Checked {
    Checked {
        holds: satisfies(lts, i, formula, label),
        exact: !lts.is_truncated(),
    }
}

/// A shortest labelled path from the initial state to some state satisfying
/// `pred`, as `(firing channel, state)` steps. `Some(vec![])` if the initial
/// state already satisfies `pred`; `None` if no such state is reachable.
pub fn shortest_path<P: Fn(usize) -> bool>(lts: &Lts, pred: P) -> Option<Vec<(Name, usize)>> {
    let init = lts.initial();
    if pred(init) {
        return Some(Vec::new());
    }
    let n = lts.num_states();
    let mut prev: Vec<Option<(usize, Name)>> = vec![None; n];
    let mut visited = vec![false; n];
    visited[init] = true;
    let mut queue = VecDeque::new();
    queue.push_back(init);

    while let Some(u) = queue.pop_front() {
        for t in lts.transitions(u) {
            if visited[t.target] {
                continue;
            }
            visited[t.target] = true;
            prev[t.target] = Some((u, t.label.clone()));
            if pred(t.target) {
                let mut path = Vec::new();
                let mut cur = t.target;
                while let Some((p, lbl)) = prev[cur].clone() {
                    path.push((lbl, cur));
                    if p == init {
                        break;
                    }
                    cur = p;
                }
                path.reverse();
                return Some(path);
            }
            queue.push_back(t.target);
        }
    }
    None
}

/// A counterexample to an invariant: a shortest run from the initial state to a
/// reachable state where `invariant` fails, or `None` if it holds everywhere
/// reachable.
pub fn counterexample<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    invariant: &Formula,
    label: &L,
) -> Option<Vec<(Name, usize)>> {
    let good = check(lts, invariant, label);
    shortest_path(lts, |i| !good[i])
}

/// A witness for a reachability goal: a shortest run from the initial state to a
/// state satisfying `goal`, or `None` if unreachable.
pub fn witness<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    goal: &Formula,
    label: &L,
) -> Option<Vec<(Name, usize)>> {
    let sat = check(lts, goal, label);
    shortest_path(lts, |i| sat[i])
}
