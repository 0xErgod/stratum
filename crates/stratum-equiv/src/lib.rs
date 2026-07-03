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
//!
//! ## Algorithm
//!
//! Both bisimulations are decided by **relational coarsest-partition
//! refinement** (Kanellakis–Smolka style: iterated signature refinement) over
//! the disjoint-union reduction graph of the two explored processes. Because the
//! current N-barbed semantics matches a move to a move purely by the relation on
//! *targets* (labels are ignored) and existentially both ways, bisimilarity of
//! the combined LTS is exactly the coarsest partition in which two states share
//! a block iff (a) they carry the same barb signature and (b) they have equal
//! *sets* of successor blocks. The two initial states are equivalent iff they
//! land in the same block.
//!
//! * **Strong** (`~N`): edges are single reduction steps; the initial signature
//!   is each state's [`strong_barbs`] set. This is the case that improves on the
//!   old cross-product fixpoint (see [`refine`] for the cost).
//! * **Weak** (`≈N`): edges are the reflexive-transitive (τ*) *saturation* of
//!   reduction; the initial signature is each state's weak-barb set (the union
//!   of strong barbs over all τ*-reachable states). Refining strongly over the
//!   saturated graph reproduces the paper's `≈N`. Note that saturation densifies
//!   the edge set to O(n²), so the weak mode is *not* asymptotically cheaper than
//!   the old procedure — the genuine asymptotic win is in the strong mode.
//!
//! The previous cross-product greatest-fixpoint decision procedure is retained
//! (hidden) in [`naive`] as a reference oracle for differential testing.

use std::collections::{BTreeSet, HashMap};

use stratum_core::{canonicalize_name, name_equiv, Name, Proc};
use stratum_lts::{format_name, Lts};

pub mod labelled_bisim;
pub use labelled_bisim::{strong_labelled_bisimilar, weak_labelled_bisimilar};

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
pub fn weak_barbed_bisimilar(p: &Proc, q: &Proc, observations: &[Name], bound: usize) -> Verdict {
    bisimilar(p, q, observations, bound, Mode::Weak)
}

/// Strong N-barbed bisimulation: step-for-step matching with strong barbs.
pub fn strong_barbed_bisimilar(p: &Proc, q: &Proc, observations: &[Name], bound: usize) -> Verdict {
    bisimilar(p, q, observations, bound, Mode::Strong)
}

/// Decide `P ~N Q` (strong) or `P ≈N Q` (weak) by partition refinement over the
/// disjoint union of the two explored reduction graphs.
fn bisimilar(p: &Proc, q: &Proc, observations: &[Name], bound: usize, mode: Mode) -> Verdict {
    let lts1 = Lts::explore(p, bound);
    let lts2 = Lts::explore(q, bound);
    if lts1.is_truncated() || lts2.is_truncated() {
        return Verdict::Inconclusive("state space exceeded the exploration bound".into());
    }

    let obs: Vec<Name> = observations.iter().map(canonicalize_name).collect();
    let n1 = lts1.num_states();
    let n2 = lts2.num_states();
    let n = n1 + n2;

    // Per-state strong barbs over the combined (disjoint-union) state space:
    // states `0..n1` are `lts1`, states `n1..n` are `lts2` offset by `n1`.
    let mut sbarbs: Vec<BTreeSet<Name>> = Vec::with_capacity(n);
    for i in 0..n1 {
        sbarbs.push(strong_barbs(lts1.state(i), &obs));
    }
    for j in 0..n2 {
        sbarbs.push(strong_barbs(lts2.state(j), &obs));
    }

    // Combined edge relation. Strong: single reduction steps. Weak: the τ*
    // saturation (reflexive-transitive closure), so a weak move `⇒` is a single
    // edge and refining strongly over it yields weak bisimulation.
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); n];
    // Signature (initial partition key) per state: strong barbs for the strong
    // relation, weak barbs (union over τ*-reachable states) for the weak one.
    let mut sig: Vec<BTreeSet<Name>> = vec![BTreeSet::new(); n];

    match mode {
        Mode::Strong => {
            for i in 0..n1 {
                edges[i] = dedup_targets(lts1.transitions(i).iter().map(|t| t.target));
                sig[i] = sbarbs[i].clone();
            }
            for j in 0..n2 {
                edges[n1 + j] = dedup_targets(lts2.transitions(j).iter().map(|t| n1 + t.target));
                sig[n1 + j] = sbarbs[n1 + j].clone();
            }
        }
        Mode::Weak => {
            let fill = |lts: &Lts,
                        offset: usize,
                        edges: &mut Vec<Vec<usize>>,
                        sig: &mut Vec<BTreeSet<Name>>| {
                for s in 0..lts.num_states() {
                    let reach = reachable_set(lts, s);
                    let mut ws = Vec::new();
                    let mut wbarb = BTreeSet::new();
                    for (k, r) in reach.iter().enumerate() {
                        if *r {
                            ws.push(offset + k);
                            wbarb.extend(sbarbs[offset + k].iter().cloned());
                        }
                    }
                    edges[offset + s] = ws;
                    sig[offset + s] = wbarb;
                }
            };
            fill(&lts1, 0, &mut edges, &mut sig);
            fill(&lts2, n1, &mut edges, &mut sig);
        }
    }

    let block = refine(n, &edges, &sig);

    let init1 = lts1.initial();
    let init2 = n1 + lts2.initial();
    if block[init1] == block[init2] {
        Verdict::Equivalent
    } else if sig[init1] != sig[init2] {
        // Deliberate: for the strong relation this reports differing *strong*
        // barbs (the mode's signature), not weak barbs as the old oracle did —
        // the more accurate diagnostic for a strong distinction. Discriminant
        // (Equivalent vs not) is unaffected.
        let kind = match mode {
            Mode::Strong => "strong",
            Mode::Weak => "weak",
        };
        Verdict::Distinguished(format!(
            "initial {kind} barbs differ: {} vs {}",
            fmt_barbs(&sig[init1]),
            fmt_barbs(&sig[init2]),
        ))
    } else {
        Verdict::Distinguished(
            "no N-barbed bisimulation relates the initial states (branching differs)".into(),
        )
    }
}

/// Sorted, de-duplicated successor indices.
fn dedup_targets(it: impl Iterator<Item = usize>) -> Vec<usize> {
    let mut v: Vec<usize> = it.collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// Relational coarsest partition of a graph on `n` nodes.
///
/// Starting from the initial partition induced by `sig`, iteratively split every
/// block so that two nodes share a block only if they have the same *set* of
/// successor blocks. Splitting is monotone (blocks only ever subdivide), so the
/// fixpoint is the coarsest partition stable under the reduction relation — the
/// bisimulation on the combined LTS. Returns the block id of each node.
///
/// This is the plain Kanellakis–Smolka scheme: each round rebuilds a signature
/// map for all `n` nodes, and there can be up to `n` rounds (one per split), so
/// the cost is `O(rounds · Σdeg) = O(n · Σdeg)` — no `O(m log n)` Paige–Tarjan
/// counter/three-way-split machinery here. It still beats the old ~`O(n⁴)`
/// cross-product fixpoint for the *strong* relation, where `Σdeg` is the number
/// of reduction steps; for the *weak* relation the τ*-saturated edge set is
/// dense (`Σdeg = O(n²)`), so there is no asymptotic gain there.
fn refine(n: usize, edges: &[Vec<usize>], sig: &[BTreeSet<Name>]) -> Vec<usize> {
    // Seed blocks from the barb signatures.
    let mut block = vec![0usize; n];
    {
        let mut seed: HashMap<&BTreeSet<Name>, usize> = HashMap::new();
        for (s, sg) in sig.iter().enumerate().take(n) {
            let next = seed.len();
            block[s] = *seed.entry(sg).or_insert(next);
        }
    }
    let mut num_blocks = block.iter().copied().max().map_or(0, |m| m + 1);

    loop {
        let mut sig_map: HashMap<(usize, Vec<usize>), usize> = HashMap::new();
        let mut next_block = vec![0usize; n];
        for (s, next_slot) in next_block.iter_mut().enumerate() {
            let mut succ: Vec<usize> = edges[s].iter().map(|&t| block[t]).collect();
            succ.sort_unstable();
            succ.dedup();
            let key = (block[s], succ);
            let id = sig_map.len();
            *next_slot = *sig_map.entry(key).or_insert(id);
        }
        let new_count = sig_map.len();
        block = next_block;
        if new_count == num_blocks {
            break; // no block split this round: stable.
        }
        num_blocks = new_count;
    }
    block
}

fn fmt_barbs(barbs: &BTreeSet<Name>) -> String {
    if barbs.is_empty() {
        "{}".to_string()
    } else {
        let items: Vec<String> = barbs.iter().map(format_name).collect();
        format!("{{{}}}", items.join(", "))
    }
}

/// Reference implementation retained for differential testing.
///
/// This is the original O(n²)-relation greatest-fixpoint decision procedure over
/// the A×B cross product. The public [`strong_barbed_bisimilar`] /
/// [`weak_barbed_bisimilar`] use partition refinement instead; this module lets
/// the test suite cross-check the two on random systems. Hidden from the docs
/// and not part of the supported API.
#[doc(hidden)]
pub mod naive {
    use super::{fmt_barbs, reachable_set, strong_barbs, BTreeSet, Lts, Mode, Name, Proc, Verdict};
    use stratum_core::canonicalize_name;

    /// Strong N-barbed bisimulation via the cross-product fixpoint (oracle).
    pub fn strong_barbed_bisimilar(
        p: &Proc,
        q: &Proc,
        observations: &[Name],
        bound: usize,
    ) -> Verdict {
        bisimilar(p, q, observations, bound, Mode::Strong)
    }

    /// Weak N-barbed bisimulation via the cross-product fixpoint (oracle).
    pub fn weak_barbed_bisimilar(
        p: &Proc,
        q: &Proc,
        observations: &[Name],
        bound: usize,
    ) -> Verdict {
        bisimilar(p, q, observations, bound, Mode::Weak)
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

        let barb_ok = |i: usize, j: usize| match mode {
            Mode::Strong => sb1[i] == sb2[j],
            Mode::Weak => sb1[i].is_subset(&wb2[j]) && sb2[j].is_subset(&wb1[i]),
        };

        let mut r: Vec<Vec<bool>> = (0..n1)
            .map(|i| (0..n2).map(|j| barb_ok(i, j)).collect())
            .collect();

        loop {
            let mut changed = false;
            for i in 0..n1 {
                for j in 0..n2 {
                    if r[i][j] && !transfer_ok(&lts1, &lts2, &r, &reach1[i], &reach2[j], i, j, mode)
                    {
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
}
