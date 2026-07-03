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
use crate::term::{Name, Proc};

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

/// Every Comm redex of `p`, as `(firing channel, message ⌜Q⌝, reduct)` triples,
/// without deduplication.
///
/// A redex is a lift `x0⟨|Q|⟩` and an input `x1(y).P` among the active parallel
/// components with `x0 ≡N x1`; it reduces to `P{⌜Q⌝/y}` (semantic substitution,
/// §2.7), left in parallel with the untouched components. The message `⌜Q⌝` is
/// the reified name the receiver binds to `y`. The firing channel and message are
/// returned raw; callers wanting stable labels pass them through
/// [`canonicalize_name`]. Reducts are nominal.
fn redexes(p: &Proc) -> Vec<(Name, Name, Proc)> {
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
            if !name_equiv(x0, x1) {
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
    let mut succ = Vec::new();
    let mut seen = HashSet::new();
    for (_label, _message, cand) in redexes(p) {
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
    let mut succ = Vec::new();
    let mut seen = HashSet::new();
    for (label, message, cand) in redexes(p) {
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
    states
}
