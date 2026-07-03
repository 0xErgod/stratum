//! On-the-fly (lazy) model checking for the **reachability / safety** fragment,
//! with **early exit** and a witness / counterexample run.
//!
//! The denotational checker in [`crate::check`] first materializes the *whole*
//! bounded reachable [`Lts`](stratum_lts::Lts), then evaluates a formula over it
//! by fixpoint iteration. For a reachability goal (`EF φ`) or a safety invariant
//! (`AG φ`) that is *shallow* — decided a few steps in — building the entire
//! (possibly exponential or unbounded) state space first is wasteful: the
//! verdict is already determined by a tiny prefix of the exploration.
//!
//! This module is the **lazy dual** for that fragment. It drives the exploration
//! directly through [`stratum_core::step_labeled`] + [`stratum_core::canonicalize`]
//! — exactly as [`Lts::explore`](stratum_lts::Lts::explore) does, same
//! breadth-first order, same congruence dedup — but **checks the property as each
//! state is discovered and STOPS the instant the verdict is decided**:
//!
//! * [`find_reachable`] (reachability, `EF goal`): the moment a state satisfying
//!   the goal predicate is discovered, exploration stops and the path to it is
//!   returned as a [`Run`] — the rest of the state space is never built.
//! * [`check_safety`] (safety, `AG invariant`): the moment a state *violating*
//!   the invariant is discovered, exploration stops and the violating run is
//!   returned as a counterexample. If exploration completes within the bound with
//!   no violation, the invariant holds over the explored fragment; the verdict is
//!   *definitive* only if the fragment is the whole reachable space (the bound was
//!   not hit), mirroring the [`Checked`](crate::check::Checked) exactness notion.
//!
//! # Agreement with the full checker
//!
//! Both explorers create states in the **same order** (breadth-first, same
//! `step_labeled` enumeration, same canonical-form dedup, same `>= bound`
//! truncation rule), so for a given `bound` the on-the-fly reachable prefix is a
//! prefix of [`Lts::explore`](stratum_lts::Lts::explore)'s state set. Hence, over
//! the same bound:
//!
//! * a reachability witness exists **iff**
//!   `holds(&Lts::explore(start, bound), &ef(prop), &label)` — and the returned
//!   [`Run`] is a genuine shortest reduction sequence to a goal state (BFS, like
//!   [`shortest_path`](crate::check::shortest_path));
//! * a safety counterexample exists **iff**
//!   `counterexample(&lts, &inv, &label)` finds one (equivalently `!holds(ag(inv))`).
//!
//! A positive reachability witness and a safety counterexample are *sound under
//! truncation* (they are real reachable runs); a negative reachability verdict or
//! a "safety holds" verdict is *definitive* only when the fragment was fully
//! explored. This is the same polarity-soundness reasoning documented on
//! [`Checked`](crate::check::Checked), surfaced here as the `exact` field.

use std::collections::{HashMap, VecDeque};

use stratum_core::{canonicalize, step_labeled, Name, Proc};

/// One step of an on-the-fly [`Run`]: the canonical firing channel and message
/// of the `Comm`, and the canonical state reached after the step.
///
/// Mirrors a [`Transition`](stratum_lts::Transition), but records the target
/// **state** inline (there is no owning `Lts` to index into) so the run is
/// self-contained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunStep {
    /// The `≡N`-canonical channel the `Comm` fired on.
    pub channel: Name,
    /// The `≡N`-canonical message transmitted by the `Comm`.
    pub message: Name,
    /// The `≡`-canonical state reached after this step.
    pub state: Proc,
}

/// A genuine reduction sequence from a `start` state, as produced by the
/// on-the-fly explorers.
///
/// The empty run (`steps` is empty) means the `start` state itself already
/// satisfies the queried predicate. Each step is a real ρ-calculus `Comm`
/// discovered during exploration, so the run is a witness / counterexample that
/// stays sound even when exploration was truncated (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Run {
    /// The `≡`-canonical initial state the run departs from.
    pub start: Proc,
    /// The steps of the run, in order; empty iff `start` already qualifies.
    pub steps: Vec<RunStep>,
}

impl Run {
    /// The number of `Comm` steps in the run.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the run is empty — i.e. the `start` state already qualifies.
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    /// The final (canonical) state of the run — `start` if the run is empty.
    pub fn last_state(&self) -> &Proc {
        self.steps.last().map_or(&self.start, |s| &s.state)
    }

    /// The sequence of firing channels along the run.
    pub fn channels(&self) -> Vec<Name> {
        self.steps.iter().map(|s| s.channel.clone()).collect()
    }
}

/// The result of an on-the-fly **reachability** query ([`find_reachable`]).
#[derive(Clone, Debug)]
pub struct Reachability {
    /// A shortest run to a goal state, or `None` if none was found within the
    /// explored fragment. A `Some` witness is a genuine reachable run, definitive
    /// regardless of truncation.
    pub witness: Option<Run>,
    /// The number of distinct states created before the search stopped. With
    /// early exit this is typically far smaller than the full reachable space.
    pub explored: usize,
    /// Whether the verdict is definitive. Always `true` when a witness was found
    /// (a reachability witness is sound under truncation); for a *negative*
    /// verdict, `true` only if the whole reachable space was explored within the
    /// bound (no truncation) — mirrors [`Checked::exact`](crate::check::Checked).
    pub exact: bool,
}

impl Reachability {
    /// Whether a goal state was reached (a witness exists).
    pub fn reached(&self) -> bool {
        self.witness.is_some()
    }
}

/// The result of an on-the-fly **safety** query ([`check_safety`]).
#[derive(Clone, Debug)]
pub struct Safety {
    /// A shortest run to a state violating the invariant, or `None` if no
    /// violation was found within the explored fragment. A `Some` counterexample
    /// is a genuine bad run, definitive regardless of truncation.
    pub counterexample: Option<Run>,
    /// The number of distinct states created before the search stopped. With
    /// early exit this is typically far smaller than the full reachable space.
    pub explored: usize,
    /// Whether the verdict is definitive. Always `true` when a counterexample was
    /// found (a safety counterexample is sound under truncation); for a *holds*
    /// verdict, `true` only if the whole reachable space was explored within the
    /// bound (no truncation) — mirrors [`Checked::exact`](crate::check::Checked).
    pub exact: bool,
}

impl Safety {
    /// Whether the invariant holds over the explored fragment (no counterexample
    /// was found). Combine with [`Safety::exact`] for a definitive verdict.
    pub fn holds(&self) -> bool {
        self.counterexample.is_none()
    }
}

/// The outcome of the shared lazy breadth-first search.
struct Search {
    /// Index of the first state satisfying the stop predicate, if any.
    found: Option<usize>,
    /// Number of distinct states created before stopping.
    explored: usize,
    /// Whether exploration hit the `bound` (so states were dropped).
    truncated: bool,
    /// The canonical states, in discovery order (state `0` is `start`).
    states: Vec<Proc>,
    /// Back-pointers for path reconstruction: `prev[i] = Some((parent, channel,
    /// message))` for the edge that first discovered state `i`; `None` for
    /// `start`.
    prev: Vec<Option<(usize, Name, Name)>>,
}

/// Lazy breadth-first exploration from `start`, bounded by `bound` distinct
/// states, stopping the instant a discovered state satisfies `stop`.
///
/// Deliberately mirrors [`Lts::explore`](stratum_lts::Lts::explore): the frontier
/// is stepped as *nominal* representatives while *canonical* forms are the
/// identity keys, states are created in the same order, and a new target beyond
/// `bound` sets truncation and is skipped. The only additions are the `stop`
/// check on each newly discovered state (and on `start`) and the early return —
/// so the created-state prefix matches `Lts::explore`'s exactly, which is what
/// makes the verdicts agree.
fn explore_until<S: Fn(&Proc) -> bool>(start: &Proc, bound: usize, stop: &S) -> Search {
    let start_canon = canonicalize(start);
    let mut states: Vec<Proc> = vec![start_canon.clone()];
    let mut index: HashMap<Proc, usize> = HashMap::new();
    index.insert(start_canon.clone(), 0);
    let mut prev: Vec<Option<(usize, Name, Name)>> = vec![None];

    // The start state may already decide the verdict (a zero-length run).
    if stop(&start_canon) {
        return Search {
            found: Some(0),
            explored: 1,
            truncated: false,
            states,
            prev,
        };
    }

    let mut truncated = false;
    let mut queue: VecDeque<(usize, Proc)> = VecDeque::new();
    queue.push_back((0, start.clone()));

    while let Some((from, rep)) = queue.pop_front() {
        for step in step_labeled(&rep) {
            let key = canonicalize(&step.reduct);
            if index.contains_key(&key) {
                continue; // already discovered — BFS keeps the first (shortest) path.
            }
            if states.len() >= bound {
                truncated = true;
                continue; // bound hit — drop this target, exactly as `Lts::explore`.
            }
            let t = states.len();
            index.insert(key.clone(), t);
            states.push(key.clone());
            prev.push(Some((from, step.channel.clone(), step.message.clone())));
            if stop(&key) {
                // Early exit: the verdict is decided; do not explore further.
                return Search {
                    found: Some(t),
                    explored: states.len(),
                    truncated,
                    states,
                    prev,
                };
            }
            queue.push_back((t, step.reduct));
        }
    }

    let explored = states.len();
    Search {
        found: None,
        explored,
        truncated,
        states,
        prev,
    }
}

/// Reconstruct the run from `start` (state `0`) to `target` by walking the
/// discovery back-pointers, exactly as [`shortest_path`](crate::check::shortest_path)
/// does — yielding a genuine shortest reduction sequence.
fn reconstruct(search: &Search, target: usize) -> Run {
    let mut steps = Vec::new();
    let mut cur = target;
    while let Some((parent, channel, message)) = search.prev[cur].clone() {
        steps.push(RunStep {
            channel,
            message,
            state: search.states[cur].clone(),
        });
        cur = parent;
    }
    steps.reverse();
    Run {
        start: search.states[0].clone(),
        steps,
    }
}

/// On-the-fly **reachability**: is a state satisfying `goal` reachable from
/// `start`? Explores lazily, breadth-first, up to `bound` distinct states, and
/// **stops at the first goal state discovered**, returning a shortest witness run
/// to it — without building the rest of the state space.
///
/// This is the lazy dual of `holds(&lts, &ef(prop), &label)` + [`witness`]: over
/// the same `bound` the [`Reachability::reached`] verdict agrees with the full
/// checker, and a returned [`Run`] is a genuine reachable path (sound even under
/// truncation). See the module docs for the agreement argument.
///
/// [`witness`]: crate::check::witness
pub fn find_reachable<G: Fn(&Proc) -> bool>(start: &Proc, bound: usize, goal: G) -> Reachability {
    let search = explore_until(start, bound, &goal);
    let witness = search.found.map(|t| reconstruct(&search, t));
    // A positive reachability verdict is definitive; a negative one only if the
    // reachable space was fully explored within the bound.
    let exact = witness.is_some() || !search.truncated;
    Reachability {
        witness,
        explored: search.explored,
        exact,
    }
}

/// On-the-fly **safety**: does `invariant` hold on every state reachable from
/// `start`? Explores lazily, breadth-first, up to `bound` distinct states, and
/// **stops at the first state that violates the invariant**, returning a shortest
/// counterexample run to it — without building the rest of the state space.
///
/// This is the lazy dual of `counterexample(&lts, &inv, &label)` (equivalently
/// `holds(&lts, &ag(inv), &label)`): over the same `bound` the
/// [`Safety::holds`] verdict agrees with the full checker, a returned
/// counterexample [`Run`] is a genuine bad run (sound even under truncation), and
/// a "holds" verdict is definitive exactly when [`Safety::exact`] is `true`. See
/// the module docs for the agreement argument.
pub fn check_safety<I: Fn(&Proc) -> bool>(start: &Proc, bound: usize, invariant: I) -> Safety {
    // A counterexample is a *violation* of the invariant.
    let violated = |p: &Proc| !invariant(p);
    let search = explore_until(start, bound, &violated);
    let counterexample = search.found.map(|t| reconstruct(&search, t));
    // A counterexample is definitive; "holds" only if fully explored.
    let exact = counterexample.is_some() || !search.truncated;
    Safety {
        counterexample,
        explored: search.explored,
        exact,
    }
}

/// [`find_reachable`] phrased over a labelling, consistent with the full checker:
/// the goal is the atomic proposition `goal_prop` under `label`, i.e. the lazy
/// dual of `holds(&lts, &ef(prop(goal_prop)), &label)`.
pub fn find_reachable_prop<L: Fn(&str, &Proc) -> bool>(
    start: &Proc,
    bound: usize,
    goal_prop: &str,
    label: L,
) -> Reachability {
    find_reachable(start, bound, |p: &Proc| label(goal_prop, p))
}

/// [`check_safety`] phrased over a labelling, consistent with the full checker:
/// the invariant is the atomic proposition `inv_prop` under `label`, i.e. the
/// lazy dual of `holds(&lts, &ag(prop(inv_prop)), &label)`.
pub fn check_safety_prop<L: Fn(&str, &Proc) -> bool>(
    start: &Proc,
    bound: usize,
    inv_prop: &str,
    label: L,
) -> Safety {
    check_safety(start, bound, |p: &Proc| label(inv_prop, p))
}
