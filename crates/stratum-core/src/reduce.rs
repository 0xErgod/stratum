//! One-step reduction — the operational semantics of §2.8.
//!
//! ```text
//!            x0 ≡N x1
//! ─────────────────────────────────  (Comm)
//! x0⟨|Q|⟩ | x1(y).P  →  P{⌜Q⌝/y}
//! ```
//!
//! with the context rules
//!
//! ```text
//!   P → P'                 P ≡ P'   P' → Q'   Q' ≡ Q
//! ───────────  (Par)      ─────────────────────────  (Equiv)
//! P|Q → P'|Q                        P → Q
//! ```
//!
//! Reduction is asynchronous and *shallow*: it fires only among the active
//! parallel components and never descends under an input prefix, a lift, a
//! drop, or a quote. The `Par` and `Equiv` rules are realized here by flattening
//! the parallel components (so associativity, commutativity, and the `0` unit
//! are quotiented away) and by keying successors on their canonical form.
//!
//! The substitution in `Comm` is the *semantic* one (§2.7): the receiver binds
//! `y` to the reified name `⌜Q⌝`, and dropping it runs `Q`.
//!
//! Successors are returned as **nominal** terms (binder symbols intact) so they
//! can be reduced again; canonical forms are used only as dedup keys. This
//! matters because a canonical term reuses de Bruijn index `0` at every binder,
//! which the nominal substitution is not designed to traverse.

use std::collections::HashSet;

use crate::congruence::{canonicalize, canonicalize_name, name_equiv};
use crate::subst::subst_semantic;
use crate::term::{drop_, par, Name, Proc};

/// A labelled one-step transition of the trace LTS, as produced by
/// [`step_labeled`].
///
/// A `Comm` step `x0⟨|Q|⟩ | x1(y).P → P{⌜Q⌝/y}` is observed by *both* the
/// channel it fired on and the message it transmitted. The message is exactly the
/// reified name `⌜Q⌝` the receiver binds to `y` — a first-class trace event, not
/// merely part of the successor state. Both [`channel`](Step::channel) and
/// [`message`](Step::message) are `≡N`-canonical; the [`reduct`](Step::reduct) is
/// nominal so it can be stepped again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Step {
    /// The `≡N`-canonical channel the `Comm` fired on.
    pub channel: Name,
    /// The `≡N`-canonical message transmitted — the reified name `⌜Q⌝`.
    pub message: Name,
    /// The nominal successor process `P{⌜Q⌝/y}`.
    pub reduct: Proc,
}

/// The synchronization test parameterizing the `Comm` rule (§2.8).
///
/// The paper's communication rule fires `x0⟨|Q|⟩ | x1(y).P` exactly when the
/// sending and receiving channels are a *channel / co-channel pair*. §2.8 leaves
/// which pairs qualify as a **parameter** of the calculus: the default reading
/// takes it to be name equivalence `≡N` ([`NameEquiv`]), while §2.8 also names
/// the *Comm-annihilation* family ([`Annihilation`]), in which two channels pair
/// up when their dropped processes annihilate.
///
/// A `SyncRule` implementation is the guard the [`redexes_with`] / [`step_with`] /
/// [`step_labeled_with`] family consults in place of the hard-wired
/// `name_equiv(x0, x1)`. Implementations should be *symmetric*
/// (`synchronize(a, b) == synchronize(b, a)`) and *total* (never panic), but the
/// reducer does not rely on either for memory safety.
///
/// The un-suffixed [`step`] / [`step_labeled`] entry points fix this parameter
/// to [`NameEquiv`], so the default operational semantics — and every existing
/// caller — is byte-for-byte unchanged.
pub trait SyncRule {
    /// Whether a lift on `sender_chan` may communicate with an input on
    /// `receiver_chan` — i.e. whether the two are a channel / co-channel pair.
    fn synchronize(&self, sender_chan: &Name, receiver_chan: &Name) -> bool;
}

/// The default synchronization rule: name equivalence `≡N` (§2.4, §2.8).
///
/// `synchronize(x0, x1)` is exactly `name_equiv(x0, x1)`, so reducing with
/// `NameEquiv` reproduces the standard `Comm` rule — and hence the behavior of
/// the un-suffixed [`step`] and [`step_labeled`] — exactly.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct NameEquiv;

impl SyncRule for NameEquiv {
    #[inline]
    fn synchronize(&self, sender_chan: &Name, receiver_chan: &Name) -> bool {
        name_equiv(sender_chan, receiver_chan)
    }
}

/// A bounded, decidable **under-approximation** of the §2.8 Comm-annihilation
/// family.
///
/// # The paper's rule
///
/// §2.8 parameterizes the calculus by an alternative to `≡N`: `x0` and `x1` are
/// a channel / co-channel pair when their dropped processes *annihilate*, i.e.
///
/// ```text
/// *x0 | *x1  →*  0.
/// ```
///
/// The paper's base case is that **`0` is its own co-channel**: with
/// `x0 = x1 = ⌜0⌝`, dropping runs the quoted code (§2.6), so
/// `*⌜0⌝ | *⌜0⌝` is `0 | 0 ≡ 0`, which already annihilates in zero steps.
///
/// The general condition `*x0 | *x1 →* 0` is a universal reachability property
/// of the (in general infinite) reduction graph, and is therefore
/// **undecidable**. Any executable rule must approximate it.
///
/// # What this implementation decides
///
/// [`Annihilation`] is that approximation, made honest by two design choices:
///
/// * **Drops are run — under this crate's inert-drop reduction.** Because this
///   crate keeps `*⌜P⌝` inert at the process level (drop only runs under
///   substitution — see [`crate::congruence`]), the annihilation condition is
///   evaluated on the *dropped* processes: a channel `⌜P⌝` contributes `P` to
///   the candidate `P0 | P1` (§2.6), while a still-bound name `x` contributes an
///   inert `*x`. This is what makes the `⌜0⌝ / ⌜0⌝` base case reduce to `0`.
///   Annihilation is judged w.r.t. *this* reduction only: a nested or deferred
///   drop such as `⌜*⌜0⌝⌝` — which would collapse to `0` under full ρ-reduction
///   but stays the inert `*⌜0⌝` here — is conservatively **not** recognized as
///   annihilating. That is safe under-reporting, never over-reporting.
/// * **Bounded, terminating, and robust.** `synchronize(x0, x1)` is `true` iff,
///   exploring `P0 | P1` with the ordinary (default-rule) reducer to depth
///   [`bound`](Annihilation::bound):
///     1. the exploration **settled** within the bound — judged over the
///        *whole* discovered state set (not merely its final BFS frontier):
///        every discovered state reaches a normal form along edges that stay
///        within the discovered set, so no reduction sequence runs past the
///        bound and no state sits on a non-terminating cycle; **and**
///     2. at least one such normal form is `0`, and **every** normal form is
///        `0`.
///
///   Condition (1) closes the truncation hole: a candidate with one run to `0`
///   *and* another run still reducible at the bound (or divergent — including a
///   finite cycle *left behind* the frontier) is **not** accepted, because that
///   other run's fate is unknown within the bound. See [`reachable_reporting`]
///   for the whole-set settling check.
///   Condition (2) is *robust* annihilation — every settled reduction ends at
///   `0`. If either fails (no normal form reached, a reducible state remains, or
///   some normal form is non-`0`), the verdict is a conservative `false`.
///
/// # Faithfulness
///
/// This is a **decidable under-approximation**: `synchronize` may answer `false`
/// where the undecidable paper condition would answer `true` (the bound was too
/// small to let every run reach `0`, or a non-`0` stuck state was reachable),
/// but it **never** answers `true` for a pair whose dropped processes can, under
/// this crate's reduction, reach a normal form other than `0` — including runs
/// that only resolve beyond the bound. A `true` verdict therefore certifies:
/// within `bound` steps every reduction of `P0 | P1` terminated, and all
/// terminated at `0`. Raising [`bound`](Annihilation::bound) only ever turns
/// `false` verdicts into `true` for pairs that genuinely annihilate but need
/// more steps to settle; it is opt-in and never affects the default
/// [`NameEquiv`] semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Annihilation {
    /// The reduction depth to which `*x0 | *x1` is explored. Larger bounds
    /// recognize slower annihilations at greater cost; `0` only accepts pairs
    /// that annihilate with no reduction at all (e.g. the `⌜0⌝ / ⌜0⌝` base
    /// case).
    pub bound: usize,
}

/// The process obtained by *running* a dropped name (§2.6): `*⌜P⌝` runs `P`.
///
/// A quote `⌜P⌝` yields its body `P`; a still-bound name `x` yields the inert
/// drop `*x` (which cannot reduce further on its own). This is the honest
/// process-level reading of `*x` used by [`Annihilation`].
fn dropped_process(x: &Name) -> Proc {
    match x {
        Name::Quote(p) => (**p).clone(),
        Name::Var(_) => drop_(x.clone()),
    }
}

impl SyncRule for Annihilation {
    fn synchronize(&self, sender_chan: &Name, receiver_chan: &Name) -> bool {
        // *x0 | *x1, with the two drops run to their quoted bodies (§2.6).
        let candidate = par([dropped_process(sender_chan), dropped_process(receiver_chan)]);

        // Explore with the ordinary (default-rule) reducer to the configured
        // depth. `reachable_reporting` returns canonical forms plus whether the
        // graph was left unresolved within the bound.
        let (states, truncated) = reachable_reporting(&candidate, self.bound);

        // If exploration did not settle — judged over the whole discovered set:
        // some discovered state has an unexplored successor (budget exhausted)
        // or lies on a non-terminating cycle — we cannot certify robust
        // annihilation: conservatively decline. This is what keeps `synchronize`
        // an honest UNDER-approximation — a candidate with one run to `0` but
        // another run still live at the bound (anywhere in the graph, not only on
        // the final frontier) is not reported as annihilating.
        if truncated {
            return false;
        }

        // Every reduction settled within the bound: annihilation holds iff at
        // least one normal form is `0` and none is anything else. `0`
        // canonicalizes to `Proc::Zero`.
        let mut saw_zero = false;
        for state in states {
            if is_normal_form(&state) {
                if state == Proc::Zero {
                    saw_zero = true;
                } else {
                    // A reachable non-`0` normal form: not a robust annihilation.
                    return false;
                }
            }
        }
        saw_zero
    }
}

/// Flatten `p` into its active parallel components, dropping units `0` and
/// splicing nested parallels (§2.3), without descending under any prefix.
fn parallel_components(p: &Proc, out: &mut Vec<Proc>) {
    match p {
        Proc::Zero => {}
        Proc::Par(ps) => {
            for q in ps {
                parallel_components(q, out);
            }
        }
        other => out.push(other.clone()),
    }
}

/// Every Comm redex of `p` under the synchronization rule `sync`, as
/// `(firing channel, message ⌜Q⌝, reduct)` triples, without deduplication.
///
/// A redex is a lift `x0⟨|Q|⟩` and an input `x1(y).P` among the active parallel
/// components with `sync.synchronize(x0, x1)`; it reduces to `P{⌜Q⌝/y}` (semantic
/// substitution, §2.7), left in parallel with the untouched components. The
/// message `⌜Q⌝` is the reified name the receiver binds to `y`. The firing
/// channel and message are returned raw; callers wanting stable labels pass them
/// through [`canonicalize_name`]. Reducts are nominal.
///
/// With `sync = &`[`NameEquiv`] the guard is exactly `name_equiv(x0, x1)`, so
/// this reproduces the standard `Comm` rule (§2.8).
pub fn redexes_with<S: SyncRule>(p: &Proc, sync: &S) -> Vec<(Name, Name, Proc)> {
    let mut comps = Vec::new();
    parallel_components(p, &mut comps);

    let mut out = Vec::new();
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
            if !sync.synchronize(x0, x1) {
                continue;
            }

            // P{⌜Q⌝/y}: bind the receiver's name to the reified lifted process.
            // That reified name ⌜Q⌝ is exactly the transmitted message.
            let message = Name::Quote(q.clone());
            let reduced = subst_semantic(body, *bound, &message);

            // Everything except the two reactants stays in parallel.
            let mut rest: Vec<Proc> = comps
                .iter()
                .enumerate()
                .filter(|(k, _)| *k != i && *k != j)
                .map(|(_, c)| c.clone())
                .collect();
            rest.push(reduced);
            out.push((x0.clone(), message, Proc::Par(rest)));
        }
    }
    out
}

/// All one-step reducts of `p` under `Comm` (§2.8), deduplicated up to `≡`.
///
/// Each reduct is a nominal term. `p` is empty of redexes — i.e. in normal form
/// — iff the returned vector is empty (see [`is_normal_form`]).
pub fn step(p: &Proc) -> Vec<Proc> {
    step_with(p, &NameEquiv)
}

/// All one-step reducts of `p` under the synchronization rule `sync`,
/// deduplicated up to `≡`.
///
/// The generic form of [`step`], which is exactly `step_with(p, &NameEquiv)`.
/// Pass [`Annihilation`] to reduce under the §2.8 Comm-annihilation family
/// instead. Each reduct is a nominal term.
pub fn step_with<S: SyncRule>(p: &Proc, sync: &S) -> Vec<Proc> {
    let mut succ = Vec::new();
    let mut seen = HashSet::new();
    for (_label, _message, cand) in redexes_with(p, sync) {
        if seen.insert(canonicalize(&cand)) {
            succ.push(cand);
        }
    }
    succ
}

/// All one-step transitions of `p` as [`Step`]s — `(canonical firing channel,
/// canonical message ⌜Q⌝, reduct)` — deduplicated up to `≡` on channel, message,
/// and target.
///
/// This is the edge relation of the trace LTS: each [`Step`] is a labelled
/// transition tagged with the `≡N`-canonical channel the Comm fired on *and* the
/// `≡N`-canonical message it transmitted (the reified name `⌜Q⌝` bound by the
/// receiver). Reducts are nominal so they can be stepped again.
pub fn step_labeled(p: &Proc) -> Vec<Step> {
    step_labeled_with(p, &NameEquiv)
}

/// All one-step transitions of `p` as [`Step`]s under the synchronization rule
/// `sync`, deduplicated up to `≡` on channel, message, and target.
///
/// The generic form of [`step_labeled`], which is exactly
/// `step_labeled_with(p, &NameEquiv)`. Labels ([`channel`](Step::channel),
/// [`message`](Step::message)) are `≡N`-canonical regardless of `sync`; only
/// *which* redexes fire depends on `sync`. Reducts are nominal.
pub fn step_labeled_with<S: SyncRule>(p: &Proc, sync: &S) -> Vec<Step> {
    let mut succ = Vec::new();
    let mut seen = HashSet::new();
    for (label, message, cand) in redexes_with(p, sync) {
        let channel = canonicalize_name(&label);
        let message = canonicalize_name(&message);
        if seen.insert((channel.clone(), message.clone(), canonicalize(&cand))) {
            succ.push(Step {
                channel,
                message,
                reduct: cand,
            });
        }
    }
    succ
}

/// Whether `p` has no `Comm` redex (is irreducible).
pub fn is_normal_form(p: &Proc) -> bool {
    step(p).is_empty()
}

/// The set of states reachable from `start` within `max_steps` reductions, each
/// returned in canonical form.
///
/// This is a bounded breadth-first exploration of the (in general infinite)
/// reduction graph — the seed of the trace LTS to come in a later milestone.
/// The frontier is stepped as nominal representatives while canonical forms
/// serve as the visited-set keys.
pub fn reachable(start: &Proc, max_steps: usize) -> Vec<Proc> {
    reachable_reporting(start, max_steps).0
}

/// Bounded reachability, additionally reporting whether the exploration was
/// **truncated** — i.e. whether the reduction graph within `max_steps` was left
/// unresolved.
///
/// Returns `(states, truncated)` where `states` is exactly what [`reachable`]
/// returns (canonical forms). `truncated` is computed over the **whole**
/// discovered state set, independent of where any non-settling state landed in
/// the breadth-first search: it is `true` iff the exploration failed to *settle*,
/// where the discovered graph settles iff **every** discovered state reaches a
/// normal form along edges that stay within the discovered set (see
/// [`settled_within`]). A state fails to settle when one of its successors was
/// never explored — the step budget was exhausted before it was reached — or
/// when it lies on a non-terminating cycle of already-seen states (a self-loop
/// or longer back-edge admitted by canonicalization and the `P|0 ≡ P` unit law).
///
/// This whole-set formulation closes a soundness gap in the earlier
/// final-frontier-only check: a finite cycle *left behind* the frontier (dropped
/// because a sibling branch advanced strictly deeper to a normal form) was never
/// re-examined and so could be missed. Here every discovered state is judged, so
/// its BFS position is irrelevant.
///
/// `truncated == false` therefore certifies that every reduction sequence from
/// `start` reached a normal form within the bound; this is what lets
/// [`Annihilation`] soundly under-approximate annihilation. For the
/// `max_steps == 0` base case the discovered set is `{start}` itself, so a
/// `start` already in normal form (e.g. `0`) settles and is *not* truncated.
fn reachable_reporting(start: &Proc, max_steps: usize) -> (Vec<Proc>, bool) {
    let mut seen: HashSet<Proc> = HashSet::new();
    let mut states: Vec<Proc> = Vec::new();

    let start_key = canonicalize(start);
    seen.insert(start_key.clone());
    states.push(start_key);

    let mut frontier: Vec<Proc> = vec![start.clone()];
    for _ in 0..max_steps {
        let mut next = Vec::new();
        for rep in &frontier {
            for reduct in step(rep) {
                let key = canonicalize(&reduct);
                if seen.insert(key.clone()) {
                    states.push(key);
                    next.push(reduct);
                }
            }
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }

    // Truncation is decided over the WHOLE discovered set, not just the final
    // frontier: gather every discovered state's canonical successors and ask
    // whether the induced graph fully settles. A successor outside the
    // discovered set signals a budget-exhausted (un-expanded) state; a cycle of
    // discovered states that never reaches a normal form signals divergence.
    // Either leaves `settled_within` short of a full fixpoint, so `truncated`.
    let succ_keys: Vec<Vec<Proc>> = states
        .iter()
        .map(|s| step(s).iter().map(canonicalize).collect())
        .collect();
    let truncated = !settled_within(&states, &succ_keys);
    (states, truncated)
}

/// Whether the discovered reduction graph is fully **settled** — i.e. every
/// discovered state reaches a normal form along edges that stay within the
/// discovered set. `states[i]`'s canonical successors are `succ_keys[i]`.
///
/// Computed as a least fixpoint over the entire discovered set, so the verdict
/// is independent of BFS frontier position: a state settles iff every one of its
/// successors was itself discovered (equals some `states[j]`) *and* settles, with
/// a normal form (no successors) settling vacuously as the base case. A state
/// never becomes settled when a successor was never explored (the step budget was
/// exhausted before reaching it) or when it sits on a non-terminating cycle —
/// both of which leave the fixpoint short of covering every state.
///
/// The exploration is *truncated* precisely when this returns `false`.
fn settled_within(states: &[Proc], succ_keys: &[Vec<Proc>]) -> bool {
    let index: std::collections::HashMap<&Proc, usize> =
        states.iter().enumerate().map(|(i, s)| (s, i)).collect();

    let mut settling = vec![false; states.len()];
    loop {
        let mut changed = false;
        for (i, succ) in succ_keys.iter().enumerate() {
            if settling[i] {
                continue;
            }
            // Every successor must be a discovered, already-settling state.
            let all_settle = succ
                .iter()
                .all(|k| matches!(index.get(k), Some(&j) if settling[j]));
            if all_settle {
                settling[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    settling.iter().all(|&b| b)
}

#[cfg(test)]
mod truncation_tests {
    //! Whole-set truncation semantics of [`reachable_reporting`], pinned via its
    //! extracted core [`settled_within`].
    //!
    //! A genuine `*x0 | *x1` candidate cannot exhibit the target defect through
    //! the channel/annihilation machinery: a finite ρ self-loop would require a
    //! `Comm` reduct that regenerates its own consumed *input* prefix, which
    //! needs infinite syntax (the reviewer who filed #24 could not build one
    //! either). We therefore pin the underlying settling semantics directly on
    //! synthetic discovered graphs — including the exact shape the old
    //! final-frontier-only check missed: a cycle *left behind* the frontier while
    //! a sibling branch advanced deeper to a normal form.

    use super::*;
    use crate::term::{input, lift, quote, zero};

    /// The discarded final-frontier-only predicate, kept here purely so the
    /// regression can demonstrate that the *old* logic disagreed with the new
    /// whole-set logic on the left-behind-cycle graph. It inspected only the
    /// states on the final BFS frontier, reporting truncation iff one of them was
    /// still reducible (had a non-empty successor list).
    fn old_final_frontier_truncated(final_frontier_succ: &[Vec<Proc>]) -> bool {
        final_frontier_succ.iter().any(|succ| !succ.is_empty())
    }

    /// A left-behind finite cycle: a fast branch reaches a normal form (which
    /// ends up on the final frontier) while a self-looping state, discovered
    /// earlier and dropped behind the frontier, never reaches a normal form.
    ///
    /// The old final-frontier-only check inspected only `{nf}` (irreducible) and
    /// so reported settled (`truncated = false`) — the soundness gap. The
    /// whole-set check judges every state and reports `truncated = true`.
    #[test]
    fn left_behind_cycle_is_truncated_by_whole_set_check() {
        // Three structurally distinct canonical nodes (Input / Lift / Zero).
        let start = canonicalize(&input(quote(zero()), |_| zero()));
        let cycle = canonicalize(&lift(quote(zero()), zero()));
        let nf = canonicalize(&zero());
        assert_ne!(start, cycle);
        assert_ne!(cycle, nf);
        assert_ne!(start, nf);

        // start → {cycle, nf};  cycle → {cycle} (self-loop);  nf → {}.
        let states = vec![start, cycle.clone(), nf.clone()];
        let succ_keys = vec![vec![cycle.clone(), nf.clone()], vec![cycle], vec![]];

        // New whole-set logic: the self-loop never settles ⇒ truncated.
        assert!(
            !settled_within(&states, &succ_keys),
            "whole-set check must report the left-behind cycle as truncated",
        );

        // Old logic saw only the final frontier {nf}, whose successor list is
        // empty, so it wrongly reported settled (not truncated).
        assert!(
            !old_final_frontier_truncated(&[vec![]]),
            "old final-frontier-only logic wrongly reports settled on this graph",
        );
    }

    /// A fully closed, terminating graph settles (`truncated = false`): the base
    /// case the `⌜0⌝ / ⌜0⌝` candidate relies on generalizes here.
    #[test]
    fn closed_terminating_graph_settles() {
        let start = canonicalize(&input(quote(zero()), |_| zero()));
        let nf = canonicalize(&zero());
        assert_ne!(start, nf);

        // Lone normal form.
        assert!(settled_within(std::slice::from_ref(&nf), &[vec![]]));

        // start → nf → {}.
        let states = vec![start, nf.clone()];
        let succ_keys = vec![vec![nf], vec![]];
        assert!(settled_within(&states, &succ_keys));
    }

    /// A discovered state whose successor was never explored (budget exhausted)
    /// does not settle — the ordinary depth-truncation case, now handled by the
    /// same whole-set predicate.
    #[test]
    fn unexplored_successor_is_truncated() {
        let start = canonicalize(&input(quote(zero()), |_| zero()));
        let undiscovered = canonicalize(&zero());
        assert_ne!(start, undiscovered);

        // start → {undiscovered}, but `undiscovered` is absent from `states`.
        assert!(!settled_within(&[start], &[vec![undiscovered]]));
    }
}
