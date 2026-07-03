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

use std::collections::{HashMap, VecDeque};

use stratum_core::{Name, Proc};
use stratum_field::Field;
use stratum_lts::Lts;

use crate::formula::Formula;

/// A set of states as a bit vector indexed by state number.
type StateSet = Vec<bool>;

/// Per-agent information fields, keyed by agent name.
pub type Agents = HashMap<String, Field>;

fn full(n: usize) -> StateSet {
    vec![true; n]
}
fn empty(n: usize) -> StateSet {
    vec![false; n]
}

fn eval<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    f: &Formula,
    env: &mut HashMap<String, StateSet>,
    label: &L,
    agents: &Agents,
) -> StateSet {
    let n = lts.num_states();
    match f {
        Formula::True => full(n),
        Formula::False => empty(n),
        Formula::Prop(p) => (0..n).map(|i| label(p, lts.state(i))).collect(),
        Formula::NotProp(p) => (0..n).map(|i| !label(p, lts.state(i))).collect(),
        Formula::And(a, b) => {
            let sa = eval(lts, a, env, label, agents);
            let sb = eval(lts, b, env, label, agents);
            (0..n).map(|i| sa[i] && sb[i]).collect()
        }
        Formula::Or(a, b) => {
            let sa = eval(lts, a, env, label, agents);
            let sb = eval(lts, b, env, label, agents);
            (0..n).map(|i| sa[i] || sb[i]).collect()
        }
        Formula::Diamond(act, g) => {
            let sg = eval(lts, g, env, label, agents);
            (0..n)
                .map(|i| {
                    lts.transitions(i)
                        .iter()
                        .any(|t| act.matches(&t.label) && sg[t.target])
                })
                .collect()
        }
        Formula::Box(act, g) => {
            let sg = eval(lts, g, env, label, agents);
            (0..n)
                .map(|i| {
                    lts.transitions(i)
                        .iter()
                        .all(|t| !act.matches(&t.label) || sg[t.target])
                })
                .collect()
        }
        Formula::Var(x) => env.get(x).cloned().unwrap_or_else(|| empty(n)),
        Formula::Mu(x, g) => fixpoint(lts, x, g, env, label, agents, empty(n)),
        Formula::Nu(x, g) => fixpoint(lts, x, g, env, label, agents, full(n)),
        Formula::Knows(agent, g) => {
            let sg = eval(lts, g, env, label, agents);
            epistemic(lts, agent, agents, &sg, Quant::All)
        }
        Formula::Possible(agent, g) => {
            let sg = eval(lts, g, env, label, agents);
            epistemic(lts, agent, agents, &sg, Quant::Any)
        }
    }
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
    init: StateSet,
) -> StateSet {
    let saved = env.remove(x);
    let mut cur = init;
    loop {
        env.insert(x.to_string(), cur.clone());
        let next = eval(lts, body, env, label, agents);
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
/// operators.
pub fn check_epistemic<L: Fn(&str, &Proc) -> bool>(
    lts: &Lts,
    formula: &Formula,
    label: &L,
    agents: &Agents,
) -> Vec<bool> {
    let mut env = HashMap::new();
    eval(lts, formula, &mut env, label, agents)
}

/// The set of states satisfying `formula` (no epistemic agents declared).
pub fn check<L: Fn(&str, &Proc) -> bool>(lts: &Lts, formula: &Formula, label: &L) -> Vec<bool> {
    check_epistemic(lts, formula, label, &Agents::new())
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

/// A model-checking result together with whether it is *definitive*.
///
/// The μ-calculus checker runs over the bounded reachable fragment the LTS
/// explored. When the LTS was fully explored (`!Lts::is_truncated()`), the
/// reachable state space is finite and complete, so the verdict is **exact**.
/// When exploration was truncated at the state bound, the verdict is only about
/// the explored fragment (`exact == false`).
///
/// Note the sound asymmetry for the run extractors: a [`witness`] or
/// [`counterexample`] that returns `Some` is definitive even under truncation
/// (a run it found is genuinely present); only their `None` is relative to the
/// explored fragment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Checked {
    /// Whether the formula holds at the queried state, over the explored LTS.
    pub holds: bool,
    /// `true` if the LTS was fully explored, so `holds` is definitive; `false`
    /// if exploration was truncated, so `holds` is only about the fragment.
    pub exact: bool,
}

impl Checked {
    /// Whether this is a definitive verdict (the LTS was fully explored).
    pub fn is_exact(&self) -> bool {
        self.exact
    }
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
