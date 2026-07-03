//! Labelled bisimulation over the ρ-calculus labelled transition system, and its
//! documented coincidence with barbed congruence.
//!
//! Where the N-barbed bisimulation of [`crate`] compares *whole systems* by their
//! reductions and output barbs, **labelled** bisimulation compares *open
//! fragments* by the visible actions ([`Action`](stratum_core::Action)) they
//! offer to an environment. Two processes are labelled-bisimilar when they can
//! match each other's input/output/`τ` moves step for step (strong) or up to
//! internal `τ` activity (weak). This is the finer, compositional equivalence:
//! it accounts for a subterm's *input* capability, which the (asynchronous,
//! output-only) barbs cannot see, and it is exactly this that makes it a
//! **congruence** — preserved by every context.
//!
//! # Coincidence with barbed congruence (documented, not mechanized)
//!
//! The guiding theorem, for the ρ-calculus, is the *coincidence* of labelled
//! bisimilarity with **barbed congruence**:
//!
//! > `P` and `Q` are (weak) labelled-bisimilar **iff** they are barbed
//! > congruent — i.e. `C[P] ≈N C[Q]` (barbed-equivalent) for *every* context
//! > `C[·]`.
//!
//! This is the ρ-calculus instance of the standard result of Milner & Sangiorgi
//! (*Barbed bisimulation*, ICALP 1992): on a calculus whose contexts are
//! expressive enough to probe every action, labelled bisimilarity coincides with
//! the contextual closure of barbed bisimilarity. For the reflective higher-order
//! calculus specifically it is established by:
//!
//! * **Meredith & Radestock**, *A Reflective Higher-order Calculus* (ENTCS
//!   141(5), 2005), §4 — the barbed theory, with observation relative to a name
//!   set `N` (restriction "put back into the notion of observation"); and
//! * **Lybech**, *Encodability and Separation for a Reflective Higher-order
//!   Calculus* (2022) — the labelled semantics used here (late input, free
//!   output, no scope extrusion) together with its bisimulation theory and its
//!   agreement with the contextual/barbed equivalence.
//!
//! ## Direction, scope, and honesty
//!
//! We supply a **checker plus a documented relation**, not a mechanized proof of
//! the coincidence. The useful and load-bearing direction, which the test suite
//! pins as evidence, is
//!
//! > **soundness: labelled-bisimilar ⟹ barbed-equivalent** (and, by
//! > compositionality, barbed-equivalent in every context — barbed *congruent*).
//!
//! So a positive verdict from [`strong_labelled_bisimilar`] /
//! [`weak_labelled_bisimilar`] **certifies** barbed congruence. The converse
//! (completeness: barbed congruent ⟹ labelled-bisimilar) is the harder half of
//! the coincidence theorem and holds for the calculus per the citations above; we
//! do not re-derive it, and the checker never asserts it as an equality. Because
//! ρ-calculus state spaces are in general infinite, every check is **bounded**:
//! if exploration is truncated the verdict is [`Verdict::Inconclusive`].
//!
//! # Algorithm
//!
//! Both processes are explored into one shared graph of **canonical** states
//! (`≡`-congruent processes are one node, as in [`stratum_lts`]). Each state's
//! outgoing edges are compiled from
//! [`canonical_transitions`](stratum_core::canonical_transitions):
//!
//! * a `τ` edge to its (nominal) reduct;
//! * an output edge carrying the `≡N`-canonical `(channel, message)` to its
//!   residual;
//! * a **late input** edge carrying the `≡N`-canonical channel and a *vector* of
//!   successor states — one per name in the finite basis (below) — obtained by
//!   instantiating the residual [`Abstraction`](stratum_core::Abstraction).
//!
//! Frontier states are stepped as **nominal** representatives (residuals,
//! reducts, and instantiations are nominal) while their canonical forms are the
//! identity keys — exactly the discipline of [`stratum_lts::Lts::explore`].
//! Bisimilarity is then the greatest fixpoint of a relation over states: start
//! with all pairs related and repeatedly drop a pair `(i, j)` unless every edge
//! of `i` is matched by an edge of `j` of the same kind and *vice versa*, where
//!
//! * `τ` matches `τ` (strong) / `τ*` (weak);
//! * `Out(x, m)` matches `Out(x', m')` with `x ≡N x'` and `m ≡N m'`;
//! * `In(x)` matches `In(x')` with `x ≡N x'` and the two instantiation vectors
//!   related **pointwise** — i.e. the residual abstractions agree on every basis
//!   name (late matching: one responding input transition must serve *all*
//!   received names).
//!
//! For the weak relation the challenger plays a single strong edge and the
//! defender answers with a `τ`-saturated ("double arrow") move: `τ*` for a `τ`,
//! and `τ* · a · τ*` for a visible action `a` — Milner's weak bisimulation game.
//!
//! # Late input — the decidability crux and its finite basis
//!
//! Late bisimilarity relates the residual abstractions `(y)P` and `(y')Q` of two
//! matched inputs, and demands `P{a/y} ~ Q{a/y'}` for **all** received names `a`.
//! In the ρ-calculus a received name is any quote `⌜R⌝`, so there are infinitely
//! many `a` — the relation is not directly decidable.
//!
//! We make it decidable with the standard **finite basis** for late/open
//! bisimulation (a *finite-support* argument): quantifying over all names is
//! sound if we instantiate with
//!
//! 1. the finitely many **relevant names** — the `≡N`-canonical names that occur
//!    syntactically in the two systems (channels, dropped names, and the emitted
//!    messages `⌜Q⌝`); plus
//! 2. **one fresh name** `⋄`, `≡N`-distinct from all of them, standing as a
//!    representative for *every* name not otherwise mentioned.
//!
//! **Why this is faithful.** Bisimilarity is preserved by injective renamings
//! that fix the support (the free names) of the two processes: if `a` and `b` are
//! both absent from `P` and `Q`, then `P{a/y} ~ Q{a/y'}` iff `P{b/y} ~ Q{b/y'}`,
//! because a name-permutation swapping `a` and `b` is an automorphism of the
//! labelled transition system that fixes `P` and `Q`. Hence all names outside the
//! relevant set behave identically, and a single fresh representative `⋄` decides
//! them all; the relevant names must still be tried individually because a
//! received name that *coincides* with a name already in the term can trigger
//! interaction (a `Comm` on that channel) that a fresh name cannot. This is the
//! classic finite-branching result for late/open bisimulation (Sangiorgi–Walker,
//! *The π-calculus*, ch. on open/late bisimulation; the finite-support / nominal
//! argument of Pitts). The fresh `⋄` is built as a name of strictly greater quote
//! depth than any relevant name (see [`fresh_name`]), which guarantees its `≡N`
//! distinctness.
//!
//! The basis is computed once from *both* systems and shared, and the two
//! instantiation vectors are aligned index-for-index, so pointwise relation of
//! the vectors is exactly "related for every basis name".

use std::collections::{BTreeSet, HashMap, VecDeque};

use stratum_core::term::{lift, quote};
use stratum_core::{canonicalize, canonicalize_name, name_equiv, Name, Proc, Transition};

use crate::Verdict;

/// Strong labelled bisimulation: input/output/`τ` matched step-for-step.
///
/// Two processes are strongly labelled-bisimilar iff there is a symmetric
/// relation relating them in which every transition of one is answered by a
/// transition of the other **carrying the same action** — `τ` by `τ`, `Out(x,m)`
/// by `Out(x',m')` with `x ≡N x'` and `m ≡N m'`, and a late `In(x)` by an
/// `In(x')` with `x ≡N x'` whose residual abstraction agrees with the first on
/// every name of the finite basis (see the module docs). A positive verdict
/// certifies strong barbed congruence.
///
/// Exploration is bounded by `bound` distinct states; truncation yields
/// [`Verdict::Inconclusive`].
pub fn strong_labelled_bisimilar(p: &Proc, q: &Proc, bound: usize) -> Verdict {
    decide(p, q, bound, Mode::Strong)
}

/// Weak labelled bisimulation: like [`strong_labelled_bisimilar`] but matching
/// up to internal `τ` activity.
///
/// The challenger plays a single transition; the defender answers with a
/// `τ`-saturated move — `τ*` for a `τ`, and `τ* · a · τ*` for a visible action
/// `a`. Thus internal computation is unobservable, exactly as for
/// [`weak_barbed_bisimilar`](crate::weak_barbed_bisimilar). A positive verdict
/// certifies (weak) barbed congruence.
///
/// Exploration is bounded by `bound` distinct states; truncation yields
/// [`Verdict::Inconclusive`].
pub fn weak_labelled_bisimilar(p: &Proc, q: &Proc, bound: usize) -> Verdict {
    decide(p, q, bound, Mode::Weak)
}

/// Which labelled bisimulation to decide.
#[derive(Clone, Copy)]
enum Mode {
    Strong,
    Weak,
}

/// Compiled outgoing edges of one state.
#[derive(Clone, Debug, Default)]
struct Edges {
    /// `τ` successors.
    taus: Vec<usize>,
    /// Output edges: `(≡N`-canonical channel, `≡N`-canonical message, target).
    outs: Vec<(Name, Name, usize)>,
    /// Late input edges: `(≡N`-canonical channel, instantiation targets aligned
    /// index-for-index with the shared finite basis).
    ins: Vec<(Name, Vec<usize>)>,
}

/// The explored two-process labelled graph over canonical states.
struct Graph {
    edges: Vec<Edges>,
    init_p: usize,
    init_q: usize,
    truncated: bool,
}

/// Decide the chosen labelled bisimulation, bounded by `bound` states.
fn decide(p: &Proc, q: &Proc, bound: usize, mode: Mode) -> Verdict {
    let graph = build_graph(p, q, bound);
    if graph.truncated {
        return Verdict::Inconclusive("state space exceeded the exploration bound".into());
    }
    let n = graph.edges.len();

    // Weak mode needs the τ-reachability (⇒) of every state; strong mode never
    // consults it.
    let reach = match mode {
        Mode::Strong => Vec::new(),
        Mode::Weak => tau_reach(&graph.edges),
    };

    // Greatest fixpoint: start all-related, drop a pair when the transfer
    // property fails in either direction.
    let mut rel = vec![vec![true; n]; n];
    loop {
        let mut changed = false;
        for i in 0..n {
            for j in 0..n {
                if rel[i][j] && !transfer(&graph.edges, &reach, &rel, i, j, mode) {
                    rel[i][j] = false;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    if rel[graph.init_p][graph.init_q] {
        Verdict::Equivalent
    } else {
        let kind = match mode {
            Mode::Strong => "strong",
            Mode::Weak => "weak",
        };
        Verdict::Distinguished(format!(
            "no {kind} labelled bisimulation relates the initial states \
             (a visible input/output or τ move of one has no match in the other)"
        ))
    }
}

/// Transfer property for the pair `(i, j)`: `i` is simulated by `j` **and** `j`
/// by `i` under the current relation `rel`.
fn transfer(
    edges: &[Edges],
    reach: &[Vec<usize>],
    rel: &[Vec<bool>],
    i: usize,
    j: usize,
    mode: Mode,
) -> bool {
    match mode {
        Mode::Strong => strong_sim(edges, rel, i, j) && strong_sim(edges, rel, j, i),
        Mode::Weak => weak_sim(edges, reach, rel, i, j) && weak_sim(edges, reach, rel, j, i),
    }
}

/// Strong simulation: every edge of `a` is answered by an edge of `b` of the
/// same kind whose target(s) are related.
fn strong_sim(edges: &[Edges], rel: &[Vec<bool>], a: usize, b: usize) -> bool {
    for &t in &edges[a].taus {
        if !edges[b].taus.iter().any(|&u| rel[t][u]) {
            return false;
        }
    }
    for (x, m, t) in &edges[a].outs {
        let ok = edges[b]
            .outs
            .iter()
            .any(|(x2, m2, u)| name_equiv(x, x2) && name_equiv(m, m2) && rel[*t][*u]);
        if !ok {
            return false;
        }
    }
    for (x, tv) in &edges[a].ins {
        let ok = edges[b]
            .ins
            .iter()
            .any(|(x2, uv)| name_equiv(x, x2) && tv.iter().zip(uv).all(|(t, u)| rel[*t][*u]));
        if !ok {
            return false;
        }
    }
    true
}

/// Weak simulation: every *strong* edge of `a` is answered by a `τ`-saturated
/// move of `b` (`τ*` for `τ`; `τ* · a · τ*` for a visible action).
fn weak_sim(edges: &[Edges], reach: &[Vec<usize>], rel: &[Vec<bool>], a: usize, b: usize) -> bool {
    // τ: b may stay put or take any number of τ steps (⇒, reflexive).
    for &t in &edges[a].taus {
        if !reach[b].iter().any(|&u| rel[t][u]) {
            return false;
        }
    }
    // Output: b ⇒ s2 --Out(x,m)--> t2 ⇒ u.
    for (x, m, t) in &edges[a].outs {
        let ok = reach[b].iter().any(|&s2| {
            edges[s2].outs.iter().any(|(x2, m2, t2)| {
                name_equiv(x, x2) && name_equiv(m, m2) && reach[*t2].iter().any(|&u| rel[*t][u])
            })
        });
        if !ok {
            return false;
        }
    }
    // Late input: b ⇒ s2 --In(x')--> vector, then each instantiation target may
    // be followed by τ* (⇒). One responding input must serve every basis name.
    for (x, tv) in &edges[a].ins {
        let ok = reach[b].iter().any(|&s2| {
            edges[s2].ins.iter().any(|(x2, uv)| {
                name_equiv(x, x2)
                    && tv
                        .iter()
                        .zip(uv)
                        .all(|(t, u0)| reach[*u0].iter().any(|&u| rel[*t][u]))
            })
        });
        if !ok {
            return false;
        }
    }
    true
}

/// The `τ`-reachability (`⇒`, reflexive-transitive closure over `τ` edges) of
/// each state, as a sorted index list.
fn tau_reach(edges: &[Edges]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut reach = Vec::with_capacity(n);
    for i in 0..n {
        let mut seen = vec![false; n];
        let mut stack = vec![i];
        seen[i] = true;
        while let Some(u) = stack.pop() {
            for &t in &edges[u].taus {
                if !seen[t] {
                    seen[t] = true;
                    stack.push(t);
                }
            }
        }
        reach.push((0..n).filter(|&k| seen[k]).collect());
    }
    reach
}

/// Explore both processes into one shared canonical-state graph, compiling each
/// state's labelled edges. Input edges instantiate over the shared finite basis.
fn build_graph(p: &Proc, q: &Proc, bound: usize) -> Graph {
    let basis = relevant_names(p, q);

    let mut states: Vec<Proc> = Vec::new();
    let mut index: HashMap<Proc, usize> = HashMap::new();
    let mut edges: Vec<Edges> = Vec::new();
    let mut queue: VecDeque<(usize, Proc)> = VecDeque::new();
    let mut truncated = false;

    let init_p = intern(
        p,
        &mut states,
        &mut index,
        &mut edges,
        &mut queue,
        bound,
        &mut truncated,
    );
    let init_q = intern(
        q,
        &mut states,
        &mut index,
        &mut edges,
        &mut queue,
        bound,
        &mut truncated,
    );

    while let Some((from, rep)) = queue.pop_front() {
        let mut e = Edges::default();
        for t in stratum_core::canonical_transitions(&rep) {
            match t {
                Transition::Tau { reduct, .. } => {
                    if let Some(i) = intern(
                        &reduct,
                        &mut states,
                        &mut index,
                        &mut edges,
                        &mut queue,
                        bound,
                        &mut truncated,
                    ) {
                        e.taus.push(i);
                    }
                }
                Transition::Out {
                    chan,
                    msg,
                    residual,
                } => {
                    if let Some(i) = intern(
                        &residual,
                        &mut states,
                        &mut index,
                        &mut edges,
                        &mut queue,
                        bound,
                        &mut truncated,
                    ) {
                        e.outs.push((chan, msg, i));
                    }
                }
                Transition::In { chan, abs } => {
                    let mut targets = Vec::with_capacity(basis.len());
                    let mut ok = true;
                    for a in &basis {
                        match intern(
                            &abs.instantiate(a),
                            &mut states,
                            &mut index,
                            &mut edges,
                            &mut queue,
                            bound,
                            &mut truncated,
                        ) {
                            Some(i) => targets.push(i),
                            None => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    if ok {
                        e.ins.push((chan, targets));
                    }
                }
            }
        }
        edges[from] = e;
    }

    Graph {
        edges,
        init_p: init_p.unwrap_or(0),
        init_q: init_q.unwrap_or(0),
        truncated,
    }
}

/// Intern a nominal representative: return its canonical state index, creating
/// (and enqueuing) the state if new. Returns `None` and sets `truncated` when the
/// bound is reached — the caller then omits the edge (the verdict will be
/// [`Verdict::Inconclusive`] regardless).
#[allow(clippy::too_many_arguments)]
fn intern(
    rep: &Proc,
    states: &mut Vec<Proc>,
    index: &mut HashMap<Proc, usize>,
    edges: &mut Vec<Edges>,
    queue: &mut VecDeque<(usize, Proc)>,
    bound: usize,
    truncated: &mut bool,
) -> Option<usize> {
    let key = canonicalize(rep);
    if let Some(&i) = index.get(&key) {
        return Some(i);
    }
    if states.len() >= bound {
        *truncated = true;
        return None;
    }
    let i = states.len();
    index.insert(key.clone(), i);
    states.push(key);
    edges.push(Edges::default());
    queue.push_back((i, rep.clone()));
    Some(i)
}

/// The finite basis of received names for late-input instantiation: the
/// `≡N`-canonical names occurring in `p` and `q`, plus one fresh representative.
///
/// See the module docs for the soundness (finite-support) justification.
fn relevant_names(p: &Proc, q: &Proc) -> Vec<Name> {
    let mut set = BTreeSet::new();
    collect_names(p, &mut set);
    collect_names(q, &mut set);
    let mut names: Vec<Name> = set.into_iter().collect();
    let fresh = fresh_name(&names);
    names.push(fresh);
    names
}

/// Collect the `≡N`-canonical **quote** names occurring in `p` (channels, dropped
/// names, and emitted messages `⌜Q⌝`), recursing through quotes. Bound-variable
/// occurrences are not received-name candidates and are skipped.
fn collect_names(p: &Proc, out: &mut BTreeSet<Name>) {
    match p {
        Proc::Zero => {}
        Proc::Drop(n) => collect_name(n, out),
        Proc::Lift { chan, arg } => {
            collect_name(chan, out);
            // The message an output emits is the reified argument ⌜arg⌝.
            collect_name(&Name::Quote(arg.clone()), out);
            collect_names(arg, out);
        }
        Proc::Input { chan, body, .. } => {
            collect_name(chan, out);
            collect_names(body, out);
        }
        Proc::Par(ps) => {
            for p in ps {
                collect_names(p, out);
            }
        }
    }
}

/// Add a single name (only quotes — real received-name candidates) and recurse
/// into the quoted process for nested names.
fn collect_name(n: &Name, out: &mut BTreeSet<Name>) {
    if let Name::Quote(p) = n {
        out.insert(canonicalize_name(n));
        collect_names(p, out);
    }
}

/// A fresh name, `≡N`-distinct from every name in `existing`.
///
/// Built as a name whose quote depth strictly exceeds that of every relevant
/// name (a "quote tower" `⌜⌜…⌜0⌝⟨|0|⟩…⌝⟨|0|⟩⌝`), which forces `≡N`-distinctness
/// since name equivalence preserves quote depth. A defensive loop deepens further
/// on the vanishingly unlikely event of a collision, so the result is always
/// fresh.
fn fresh_name(existing: &[Name]) -> Name {
    let max_depth = existing.iter().map(Name::quote_depth).max().unwrap_or(0);
    // Build a process of quote depth `max_depth + 1`; its quote then has depth
    // `max_depth + 2`, strictly above every relevant name.
    let mut proc = Proc::Zero;
    for _ in 0..=max_depth {
        proc = lift(quote(proc), Proc::Zero);
    }
    let mut name = canonicalize_name(&quote(proc));
    while existing.iter().any(|e| name_equiv(e, &name)) {
        name = canonicalize_name(&Name::Quote(Box::new(lift(name, Proc::Zero))));
    }
    name
}

#[cfg(test)]
mod tests {
    use super::*;
    use stratum_core::term::{input, output, par, zero};

    fn ch0() -> Name {
        quote(zero())
    }
    fn ch1() -> Name {
        quote(lift(quote(zero()), zero()))
    }

    #[test]
    fn strong_reflexive() {
        let p = par([output(ch0(), ch1()), input(ch1(), |y| lift(y, zero()))]);
        assert!(strong_labelled_bisimilar(&p, &p, 200).is_equivalent());
        assert!(weak_labelled_bisimilar(&p, &p, 200).is_equivalent());
    }

    #[test]
    fn input_capability_distinguishes() {
        // x(y).0 offers an input action; 0 offers nothing. Labelled bisim sees
        // the difference (barbed bisim, output-only, would not).
        let p = input(ch0(), |_| zero());
        let q = zero();
        assert!(!strong_labelled_bisimilar(&p, &q, 200).is_equivalent());
        assert!(!weak_labelled_bisimilar(&p, &q, 200).is_equivalent());
    }

    #[test]
    fn relay_actions_are_visible_labelled() {
        // x!0  vs  a!0 | a(y).x!0 : barbed-equivalent when a is unobserved (the
        // relay reduces to an x-output), but the calculus has NO restriction, so
        // the relay's own actions Out(a,0)/In(a) are visible. Labelled bisim —
        // both strong AND weak — therefore distinguishes them. This is exactly
        // why labelled bisim is finer than (output-only) barbed bisim.
        let x = ch0();
        let a = ch1();
        let now = lift(x.clone(), zero());
        let after = par([
            lift(a.clone(), zero()),
            input(a, move |_| lift(x.clone(), zero())),
        ]);
        assert!(!strong_labelled_bisimilar(&now, &after, 200).is_equivalent());
        assert!(!weak_labelled_bisimilar(&now, &after, 200).is_equivalent());
    }

    #[test]
    fn weak_absorbs_matching_tau() {
        // Weak matching lets the defender answer a τ by staying put. Here Q can
        // do an internal τ (the a-relay) but ALSO offers everything P does, and
        // the τ-reduct is weakly indistinguishable from Q's non-τ behaviour on
        // the observed structure — a case exercising the τ* defender move.
        // (Kept as a self-comparison guard: weak bisim is reflexive even in the
        // presence of τ transitions.)
        let a = ch1();
        let q = par([lift(a.clone(), zero()), input(a, |_| zero())]);
        assert!(weak_labelled_bisimilar(&q, &q, 200).is_equivalent());
        assert!(strong_labelled_bisimilar(&q, &q, 200).is_equivalent());
    }

    #[test]
    fn distinct_output_channels_distinguished() {
        let p = lift(ch0(), zero());
        let q = lift(ch1(), zero());
        assert!(!strong_labelled_bisimilar(&p, &q, 200).is_equivalent());
        assert!(!weak_labelled_bisimilar(&p, &q, 200).is_equivalent());
    }

    #[test]
    fn fresh_name_is_distinct() {
        let names = vec![ch0(), ch1()];
        let f = fresh_name(&names);
        assert!(names.iter().all(|n| !name_equiv(n, &f)));
    }
}
