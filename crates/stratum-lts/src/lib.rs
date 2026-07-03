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

use std::collections::{HashMap, VecDeque};

use stratum_core::{canonicalize, step_labeled, Name, Proc};

/// A labelled transition to another state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition {
    /// The `≡N`-canonical channel the `Comm` fired on.
    pub label: Name,
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
            for (label, reduct) in step_labeled(&rep) {
                let key = canonicalize(&reduct);
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
                    queue.push_back((t, reduct));
                    t
                };
                transitions[from].push(Transition { label, target });
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
                    escape(&format_name(&t.label)),
                ));
            }
        }
        out.push_str("}\n");
        out
    }
}

fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
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
