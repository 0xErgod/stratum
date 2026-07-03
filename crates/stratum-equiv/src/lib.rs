//! # stratum-equiv
//!
//! Behavioral equivalences for ρ-calculus processes, following Meredith &
//! Radestock §4: **N-barbed bisimulation**, parameterized by an observation set
//! `N` of channels.
//!
//! The paper "takes restriction out of the language and puts it back into the
//! notion of observation": since all names are global, equivalence is judged
//! relative to a set `N` of channels an observer may watch. Barbs are on
//! *outputs* only — an input `x(y).P` has no barb (the calculus is asynchronous,
//! so a receiver cannot be observed):
//!
//! ```text
//!   y ∈ N,  x ≡N y                 P ↓N x  or  Q ↓N x
//! ─────────────────  (Out-barb)   ───────────────────  (Par-barb)
//!    x[v] ↓N x                          P | Q ↓N x
//! ```
//!
//! [`weak_barbed_bisimilar`] decides the paper's `≈N`: a symmetric relation `S`
//! with `P S Q` implying (i) if `P → P'` then `Q ⇒ Q'` with `P' S Q'`, and
//! (ii) if `P ↓N x` then `Q ⇓N x` (weak barb). [`strong_barbed_bisimilar`] is
//! the strong variant (step-for-step, strong barbs), and [`may_equivalent`]
//! compares the sets of weakly-observable barbs (single-barb may-testing).
//!
//! Because ρ-calculus state spaces are in general infinite, each check explores
//! both processes up to a bound; if the bound truncates either, the result is
//! [`Verdict::Inconclusive`].

use std::collections::BTreeSet;

use stratum_core::{canonicalize_name, name_equiv, Name, Proc};
use stratum_lts::{format_name, Lts};

/// The outcome of an equivalence check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The two processes are equivalent under the chosen relation and `N`.
    Equivalent,
    /// They are distinguished; the string gives a human-readable reason.
    Distinguished(String),
    /// Exploration hit the state bound, so the result is unknown.
    Inconclusive(String),
}

impl Verdict {
    /// Whether the verdict is [`Verdict::Equivalent`].
    pub fn is_equivalent(&self) -> bool {
        matches!(self, Verdict::Equivalent)
    }
}

/// Active parallel components of a (canonical) process.
fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Zero => Vec::new(),
        Proc::Par(ps) => ps.iter().collect(),
        other => vec![other],
    }
}

/// The strong barbs of `p` under observation set `obs`: the canonical channels
/// on which `p` has a top-level output that is `≡N` some observed name.
fn strong_barbs(p: &Proc, obs: &[Name]) -> BTreeSet<Name> {
    let mut set = BTreeSet::new();
    for c in components(p) {
        if let Proc::Lift { chan, .. } = c {
            if obs.iter().any(|n| name_equiv(chan, n)) {
                set.insert(canonicalize_name(chan));
            }
        }
    }
    set
}

/// The set of states reachable from `from` (including itself) by reduction.
fn reachable_set(lts: &Lts, from: usize) -> Vec<bool> {
    let mut seen = vec![false; lts.num_states()];
    let mut stack = vec![from];
    seen[from] = true;
    while let Some(u) = stack.pop() {
        for t in lts.transitions(u) {
            if !seen[t.target] {
                seen[t.target] = true;
                stack.push(t.target);
            }
        }
    }
    seen
}

/// Which bisimulation to compute.
#[derive(Clone, Copy)]
enum Mode {
    Strong,
    Weak,
}

/// Report the weakly-observable barbs of `p` (the barbs of any reachable state)
/// and whether exploration was truncated. These are the "may" observations.
pub fn may_barbs(p: &Proc, observations: &[Name], bound: usize) -> (BTreeSet<Name>, bool) {
    let lts = Lts::explore(p, bound);
    let obs: Vec<Name> = observations.iter().map(canonicalize_name).collect();
    let mut set = BTreeSet::new();
    for i in 0..lts.num_states() {
        set.extend(strong_barbs(lts.state(i), &obs));
    }
    (set, lts.is_truncated())
}

/// May-testing equivalence: `p` and `q` can weakly exhibit the same barbs.
///
/// This is the kernel of the single-barb may-testing preorder — coarser than
/// bisimulation, but a cheap first cut for "can these reach the same
/// observations?".
pub fn may_equivalent(p: &Proc, q: &Proc, observations: &[Name], bound: usize) -> Verdict {
    let (bp, tp) = may_barbs(p, observations, bound);
    let (bq, tq) = may_barbs(q, observations, bound);
    if tp || tq {
        return Verdict::Inconclusive("state space exceeded the exploration bound".into());
    }
    if bp == bq {
        Verdict::Equivalent
    } else {
        Verdict::Distinguished(format!(
            "may-barbs differ: {} vs {}",
            fmt_barbs(&bp),
            fmt_barbs(&bq)
        ))
    }
}

/// `P ≈N Q` — weak N-barbed bisimulation (§4).
pub fn weak_barbed_bisimilar(
    p: &Proc,
    q: &Proc,
    observations: &[Name],
    bound: usize,
) -> Verdict {
    bisimilar(p, q, observations, bound, Mode::Weak)
}

/// Strong N-barbed bisimulation: step-for-step matching with strong barbs.
pub fn strong_barbed_bisimilar(
    p: &Proc,
    q: &Proc,
    observations: &[Name],
    bound: usize,
) -> Verdict {
    bisimilar(p, q, observations, bound, Mode::Strong)
}

fn bisimilar(p: &Proc, q: &Proc, observations: &[Name], bound: usize, mode: Mode) -> Verdict {
    let lts1 = Lts::explore(p, bound);
    let lts2 = Lts::explore(q, bound);
    if lts1.is_truncated() || lts2.is_truncated() {
        return Verdict::Inconclusive("state space exceeded the exploration bound".into());
    }

    let obs: Vec<Name> = observations.iter().map(canonicalize_name).collect();
    let n1 = lts1.num_states();
    let n2 = lts2.num_states();

    let sb1: Vec<BTreeSet<Name>> = (0..n1).map(|i| strong_barbs(lts1.state(i), &obs)).collect();
    let sb2: Vec<BTreeSet<Name>> = (0..n2).map(|j| strong_barbs(lts2.state(j), &obs)).collect();

    // Weak reach (τ*) is needed for weak barb compatibility and weak transfer.
    let reach1: Vec<Vec<bool>> = (0..n1).map(|i| reachable_set(&lts1, i)).collect();
    let reach2: Vec<Vec<bool>> = (0..n2).map(|j| reachable_set(&lts2, j)).collect();
    let weak_barbs = |sb: &[BTreeSet<Name>], reach: &[bool]| -> BTreeSet<Name> {
        let mut s = BTreeSet::new();
        for (k, r) in reach.iter().enumerate() {
            if *r {
                s.extend(sb[k].iter().cloned());
            }
        }
        s
    };
    let wb1: Vec<BTreeSet<Name>> = (0..n1).map(|i| weak_barbs(&sb1, &reach1[i])).collect();
    let wb2: Vec<BTreeSet<Name>> = (0..n2).map(|j| weak_barbs(&sb2, &reach2[j])).collect();

    // Barb compatibility (static): a strong barb of one implies a barb of the
    // other — strong (also strong) for `Strong`, weak for `Weak`.
    let barb_ok = |i: usize, j: usize| match mode {
        Mode::Strong => sb1[i] == sb2[j],
        Mode::Weak => sb1[i].is_subset(&wb2[j]) && sb2[j].is_subset(&wb1[i]),
    };

    // R ⊆ (states of P) × (states of Q); start from all barb-compatible pairs.
    let mut r: Vec<Vec<bool>> = (0..n1)
        .map(|i| (0..n2).map(|j| barb_ok(i, j)).collect())
        .collect();

    // Greatest fixpoint: drop any pair failing the transfer property.
    loop {
        let mut changed = false;
        for i in 0..n1 {
            for j in 0..n2 {
                if r[i][j] && !transfer_ok(&lts1, &lts2, &r, &reach1[i], &reach2[j], i, j, mode) {
                    r[i][j] = false;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    if r[lts1.initial()][lts2.initial()] {
        Verdict::Equivalent
    } else if wb1[lts1.initial()] != wb2[lts2.initial()] {
        Verdict::Distinguished(format!(
            "initial weak barbs differ: {} vs {}",
            fmt_barbs(&wb1[lts1.initial()]),
            fmt_barbs(&wb2[lts2.initial()]),
        ))
    } else {
        Verdict::Distinguished(
            "no N-barbed bisimulation relates the initial states (branching differs)".into(),
        )
    }
}

/// The transfer property for the pair `(i, j)` under the current relation `r`.
#[allow(clippy::too_many_arguments)]
fn transfer_ok(
    lts1: &Lts,
    lts2: &Lts,
    r: &[Vec<bool>],
    reach_i: &[bool],
    reach_j: &[bool],
    i: usize,
    j: usize,
    mode: Mode,
) -> bool {
    // Every move of P is matched by a (weak or strong) move of Q, and vice versa.
    let p_matched = lts1.transitions(i).iter().all(|t| match mode {
        Mode::Strong => lts2.transitions(j).iter().any(|u| r[t.target][u.target]),
        Mode::Weak => (0..lts2.num_states()).any(|j2| reach_j[j2] && r[t.target][j2]),
    });
    let q_matched = lts2.transitions(j).iter().all(|u| match mode {
        Mode::Strong => lts1.transitions(i).iter().any(|t| r[t.target][u.target]),
        Mode::Weak => (0..lts1.num_states()).any(|i2| reach_i[i2] && r[i2][u.target]),
    });
    p_matched && q_matched
}

fn fmt_barbs(barbs: &BTreeSet<Name>) -> String {
    if barbs.is_empty() {
        "{}".to_string()
    } else {
        let items: Vec<String> = barbs.iter().map(format_name).collect();
        format!("{{{}}}", items.join(", "))
    }
}
