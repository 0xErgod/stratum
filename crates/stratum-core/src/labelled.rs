//! Labelled operational semantics — visible input / output actions and `τ`.
//!
//! [`crate::reduce`] gives the calculus its *reduction* relation: a `τ`-only
//! relation (the `Comm` rule, §2.8) whose observations are barbs on closed
//! terms. That is exactly what is needed to reason about a *whole* system, but
//! it says nothing about how an *open* fragment interacts with an environment
//! that is not written down. A **labelled transition system** (LTS) with visible
//! `input` and `output` actions supplies that missing half: it records what a
//! subterm can *offer to* or *receive from* its context, so two open fragments
//! can be compared for equivalence (labelled bisimulation, the next milestone)
//! without quantifying over all closing contexts.
//!
//! The theory followed here is the ρ-calculus LTS of Lybech (2022),
//! *Encodability and Separation for a Reflective Higher-Order Calculus*.
//!
//! # Actions
//!
//! ```text
//!                                   (Out)
//! x⟨|Q|⟩  --x!⌜Q⌝-->  0
//!
//!                                   (In, late)
//! x(y).P  --x?-->  (y)P
//!
//! x0⟨|Q|⟩ | x1(y).P  --τ-->  P{⌜Q⌝/y}   (x0 ≡N x1)     (Comm/τ)
//! ```
//!
//! with the structural rules that lift an action of one parallel component to
//! the whole composite (carrying the other components along), and closure under
//! `≡` (realized, as in [`crate::reduce`], by flattening the active parallel
//! components and canonicalizing labels).
//!
//! ## No bound output (free output only)
//!
//! The ρ-calculus has **no restriction operator** `ν` (§2.0.1 — the only name
//! former is the quote `⌜P⌝`). Consequently there is **no bound output** and
//! **no scope extrusion**: an output action always emits an already-formed name
//! `⌜Q⌝`, never a freshly-scoped one. This is the single largest simplification
//! over the π-calculus LTS, and it is why [`Action::Out`] carries a plain
//! [`Name`] message with no attendant binder. See the test
//! `output_is_free_never_bound`.
//!
//! ## Late (symbolic) input — and why
//!
//! For **input** there is a genuine design fork, the classic *early vs. late*
//! question. An **early** input action `x?a` would fix the received name `a` at
//! the moment of the transition and step to `P{a/y}`. But in this calculus the
//! received object may be *any* name `⌜R⌝` for any process `R`, and the set of
//! such names is infinite — so an early LTS is **infinitely branching** at every
//! input, which is unusable for a finite, decidable transition relation.
//!
//! This module therefore implements the **late / symbolic** style: an input
//! action `x?` carries no received name at all. Its residual is an
//! [`Abstraction`] `(y)P` — the open body *awaiting* a name — and the
//! substitution is deferred until the name is actually supplied (by a matching
//! output, in the `Comm`/τ rule, or by an observer in a late bisimulation game).
//! Each input thus contributes exactly **one** transition, keeping the relation
//! finitely branching and faithful. Instantiating the abstraction uses the
//! *semantic* substitution of §2.7 (see [`Abstraction::instantiate`]), so a late
//! input closed by an output reproduces the `Comm` reduct exactly — which is the
//! headline correctness property of this module (see `tau_matches_comm`).
//!
//! # Relation to [`crate::reduce`]
//!
//! The `τ` transitions produced here are, by construction, the very same
//! `Comm` redexes enumerated by [`redexes_with`](crate::reduce::redexes_with)
//! under [`NameEquiv`](crate::reduce::NameEquiv): same firing channel, same
//! transmitted message `⌜Q⌝`, same nominal reduct. A [`Transition::Tau`] mirrors
//! a [`Step`](crate::reduce::Step) field-for-field. The existing `step` /
//! `step_labeled` are left **unchanged**; this module is purely additive, and
//! the test suite pins the two `τ` relations equal over many processes.

use std::collections::HashSet;

use crate::congruence::{canonicalize, canonicalize_name, name_equiv};
use crate::subst::subst_semantic;
use crate::term::{Name, Proc};

/// The kind of a labelled action, without its residual.
///
/// This is the observation an environment makes of a single transition: an
/// input offer on a channel, a free output of a message on a channel, or an
/// invisible internal step. Channels and messages are `≡N`-canonical, so two
/// actions that differ only by a name equivalence compare equal.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Action {
    /// `x?` — a **late input** offer on channel `x`. The received name is not
    /// part of the action (see the module docs on late vs. early); it is
    /// supplied later to the transition's [`Abstraction`].
    In(Name),
    /// `x!⌜Q⌝` — a **free output** of the message `⌜Q⌝` on channel `x`. There is
    /// no bound output in this calculus (no `ν`), so both names are ordinary
    /// `≡N`-canonical names.
    Out(Name, Name),
    /// `τ` — an invisible internal communication (`Comm`, §2.8).
    Tau,
}

impl Action {
    /// The `≡N`-canonical channel this action fires on, or `None` for `τ`.
    pub fn channel(&self) -> Option<&Name> {
        match self {
            Action::In(chan) | Action::Out(chan, _) => Some(chan),
            Action::Tau => None,
        }
    }

    /// Whether this is the internal `τ` action.
    pub fn is_tau(&self) -> bool {
        matches!(self, Action::Tau)
    }
}

/// A late-input abstraction `(y)P` — an open body awaiting a received name.
///
/// This is the residual of an [`Action::In`] transition. The bound name `y` is
/// carried as its nominal binder symbol (see [`crate::term::fresh_sym`]); the
/// body `P` is kept **nominal** so it can be instantiated and then stepped
/// again. Because binder symbols are globally unique, any parallel siblings that
/// the structural rule folded into `P` are automatically `y`-free, so
/// instantiation cannot capture.
///
/// # Precondition (capture safety)
///
/// [`instantiate`](Abstraction::instantiate) substitutes for `y` across the
/// *whole* folded body `P` — the original input continuation together with the
/// untouched parallel siblings the structural rule carried in. Its
/// non-capture rests on those siblings being `y`-free. That holds for any
/// **closed** term (see [`Proc::is_closed`](crate::term::Proc::is_closed)) built
/// with the [`input`](crate::term::input) constructor: every binder draws a
/// globally-unique [`fresh_sym`](crate::term::fresh_sym), so `y` cannot already
/// occur in a sibling that was written independently. This is the same
/// invariant [`crate::reduce`] and [`crate::subst`] rely on to omit
/// α-renaming; the labelled semantics inherits rather than weakens it.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Abstraction {
    bound: u64,
    body: Proc,
}

impl Abstraction {
    /// Instantiate the abstraction with a received name, `(y)P` applied to `a`
    /// yielding `P{a/y}`.
    ///
    /// The substitution is the **semantic** one of §2.7 (see
    /// [`subst_semantic`]): dropping the received name runs the code it names.
    /// This is exactly the substitution the `Comm` rule uses, which is what
    /// makes a late input closed by an output coincide with reduction.
    pub fn instantiate(&self, received: &Name) -> Proc {
        subst_semantic(&self.body, self.bound, received)
    }

    /// The bound-name symbol `y`.
    pub fn bound(&self) -> u64 {
        self.bound
    }

    /// The (nominal) open body `P`.
    pub fn body(&self) -> &Proc {
        &self.body
    }
}

/// A single labelled transition of a process.
///
/// The three variants correspond to the three action kinds. [`Transition::Tau`]
/// is field-for-field the labelled `Comm` step of
/// [`Step`](crate::reduce::Step); [`Transition::Out`] and [`Transition::In`] are
/// the visible actions that reduction cannot see. All labels
/// ([`channel`](Transition::Out), messages) are `≡N`-canonical; every residual
/// process ([`residual`](Transition::Out), [`reduct`](Transition::Tau), and the
/// [`Abstraction`] body) is **nominal**, so it can be stepped again.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transition {
    /// `P --x?--> (y)P'` — a late input offer on `chan`, residual the
    /// abstraction `abs`.
    In {
        /// The `≡N`-canonical channel the input listens on.
        chan: Name,
        /// The `(y)P'` abstraction awaiting the received name.
        abs: Abstraction,
    },
    /// `P --x!⌜Q⌝--> P'` — a free output of `msg` on `chan`, residual `P'`.
    Out {
        /// The `≡N`-canonical channel the output emits on.
        chan: Name,
        /// The `≡N`-canonical message `⌜Q⌝` emitted (free output — never bound).
        msg: Name,
        /// The nominal residual `P'` (`0` for a bare lift, else the untouched
        /// parallel siblings).
        residual: Proc,
    },
    /// `P --τ--> P'` — an internal `Comm`. Mirrors [`Step`](crate::reduce::Step).
    Tau {
        /// The `≡N`-canonical channel the `Comm` fired on.
        channel: Name,
        /// The `≡N`-canonical message transmitted — the reified name `⌜Q⌝`.
        message: Name,
        /// The nominal successor `P{⌜Q⌝/y}`.
        reduct: Proc,
    },
}

impl Transition {
    /// The [`Action`] (label without residual) of this transition.
    pub fn action(&self) -> Action {
        match self {
            Transition::In { chan, .. } => Action::In(chan.clone()),
            Transition::Out { chan, msg, .. } => Action::Out(chan.clone(), msg.clone()),
            Transition::Tau { .. } => Action::Tau,
        }
    }

    /// Whether this is the internal `τ` transition.
    pub fn is_tau(&self) -> bool {
        matches!(self, Transition::Tau { .. })
    }
}

/// Flatten `p` into its active parallel components, dropping units `0` and
/// splicing nested parallels (§2.3), without descending under any prefix.
///
/// Mirrors the identically-named helper in [`crate::reduce`]; kept local so this
/// module is purely additive.
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

/// Rebuild a process from the components at indices other than the excluded
/// ones, applying the parallel monoid laws (a singleton collapses, the empty
/// composite is `0`).
fn par_without(comps: &[Proc], exclude: &[usize]) -> Proc {
    let rest: Vec<Proc> = comps
        .iter()
        .enumerate()
        .filter(|(k, _)| !exclude.contains(k))
        .map(|(_, c)| c.clone())
        .collect();
    match rest.len() {
        0 => Proc::Zero,
        1 => rest.into_iter().next().unwrap(),
        _ => Proc::Par(rest),
    }
}

/// All labelled transitions of `p`: the input (late), output, and `τ` actions.
///
/// The relation is built from the active parallel components of `p` (`≡` is
/// respected by flattening, as in [`crate::reduce`]), following the rules in the
/// module docs:
///
/// * **Out** — every component `x⟨|Q|⟩` offers `x!⌜Q⌝`, with residual the other
///   components (`0` when there are none). Free output only; there is no bound
///   output because the calculus has no `ν`.
/// * **In** — every component `x(y).P` offers a late `x?`, with residual the
///   abstraction `(y)(P | rest)` (the structural rule folds the untouched
///   siblings into the open body; they are `y`-free by binder freshness).
/// * **Tau** — every ordered pair of a lift `x0⟨|Q|⟩` and a distinct input
///   `x1(y).P` with `x0 ≡N x1` communicates, stepping to
///   `P{⌜Q⌝/y} | rest`. This enumeration is exactly
///   [`redexes_with`](crate::reduce::redexes_with) under
///   [`NameEquiv`](crate::reduce::NameEquiv), so the `τ` sub-relation coincides
///   with `Comm` / [`step_labeled`](crate::reduce::step_labeled).
///
/// Labels are `≡N`-canonical; residuals and abstraction bodies are nominal. The
/// list is **not** deduplicated (like `redexes_with`, and unlike
/// [`step_labeled`](crate::reduce::step_labeled)): two `≡`-identical parallel
/// components — e.g. `x⟨|0|⟩ | x⟨|0|⟩` — produce two identical output edges, and
/// likewise for `τ`. Callers that want the same edge *set* as the reduction LTS
/// (up to `≡` on the residual) should use [`canonical_transitions`] /
/// [`canonical_tau_transitions`], which deduplicate exactly as `step_labeled`
/// does.
pub fn transitions(p: &Proc) -> Vec<Transition> {
    let mut comps = Vec::new();
    parallel_components(p, &mut comps);

    let mut out = Vec::new();

    for (i, comp) in comps.iter().enumerate() {
        match comp {
            // Out: x⟨|Q|⟩ --x!⌜Q⌝--> 0, carrying the untouched siblings.
            Proc::Lift { chan, arg } => {
                let msg = Name::Quote(arg.clone());
                out.push(Transition::Out {
                    chan: canonicalize_name(chan),
                    msg: canonicalize_name(&msg),
                    residual: par_without(&comps, &[i]),
                });
            }
            // In (late): x(y).P --x?--> (y)(P | rest).
            Proc::Input { chan, bound, body } => {
                let mut abs_components = vec![(**body).clone()];
                parallel_components(&par_without(&comps, &[i]), &mut abs_components);
                let abs_body = match abs_components.len() {
                    1 => abs_components.into_iter().next().unwrap(),
                    _ => Proc::Par(abs_components),
                };
                out.push(Transition::In {
                    chan: canonicalize_name(chan),
                    abs: Abstraction {
                        bound: *bound,
                        body: abs_body,
                    },
                });
            }
            _ => {}
        }
    }

    // Tau: exactly the Comm redexes (see `redexes_with`). Enumerated here
    // compositionally as an output component synchronizing with a distinct input
    // component whose channels are ≡N — the (Comm) rule of the module docs.
    for (i, ci) in comps.iter().enumerate() {
        let Proc::Lift { chan: x0, arg: q } = ci else {
            continue;
        };
        for (j, cj) in comps.iter().enumerate() {
            if i == j {
                continue;
            }
            let Proc::Input {
                chan: x1,
                bound,
                body,
            } = cj
            else {
                continue;
            };
            if !name_equiv(x0, x1) {
                continue;
            }
            // The received message is the reified lifted process ⌜Q⌝; the late
            // input abstraction (y)(body) is instantiated with it (§2.7).
            let message = Name::Quote(q.clone());
            let reduced = subst_semantic(body, *bound, &message);
            let mut rest_components = vec![reduced];
            parallel_components(&par_without(&comps, &[i, j]), &mut rest_components);
            let reduct = match rest_components.len() {
                1 => rest_components.into_iter().next().unwrap(),
                _ => Proc::Par(rest_components),
            };
            out.push(Transition::Tau {
                channel: canonicalize_name(x0),
                message: canonicalize_name(&message),
                reduct,
            });
        }
    }

    out
}

/// Just the `τ` transitions of `p`, as [`Transition::Tau`]s.
///
/// A convenience filter over [`transitions`]. By construction this is the same
/// relation as [`step_labeled`](crate::reduce::step_labeled) (the `Comm` rule),
/// modulo the `≡`-deduplication that `step_labeled` additionally performs — the
/// property pinned by the `tau_matches_comm` test.
pub fn tau_transitions(p: &Proc) -> Vec<Transition> {
    transitions(p)
        .into_iter()
        .filter(Transition::is_tau)
        .collect()
}

/// The `≡`-canonical dedup key of a transition.
///
/// Two transitions collapse iff they agree on kind, `≡N`-canonical channel,
/// `≡N`-canonical message (outputs / `τ` only), and the `≡`-canonical form of
/// their residual. For an input the residual is the abstraction `(y)P`, keyed by
/// canonicalizing it as an `Input` on a fixed dummy channel so that
/// α-equivalent abstractions (and only those) share a key. This is exactly the
/// key [`step_labeled`](crate::reduce::step_labeled) uses for `τ`, extended to
/// the visible actions.
fn canonical_key(t: &Transition) -> (u8, Name, Option<Name>, Proc) {
    match t {
        Transition::Out {
            chan,
            msg,
            residual,
        } => (0, chan.clone(), Some(msg.clone()), canonicalize(residual)),
        Transition::In { chan, abs } => {
            // Canonicalize the abstraction body under its binder by wrapping it
            // as an Input on a fixed dummy channel (⌜0⌝); the shared dummy makes
            // the key depend only on the abstraction up to α.
            let wrapped = Proc::Input {
                chan: Name::Quote(Box::new(Proc::Zero)),
                bound: abs.bound(),
                body: Box::new(abs.body().clone()),
            };
            (1, chan.clone(), None, canonicalize(&wrapped))
        }
        Transition::Tau {
            channel,
            message,
            reduct,
        } => (
            2,
            channel.clone(),
            Some(message.clone()),
            canonicalize(reduct),
        ),
    }
}

/// All labelled transitions of `p`, **deduplicated up to `≡`** — the same edge
/// set the reduction LTS would see.
///
/// Identical to [`transitions`] except that transitions with the same
/// [`canonical_key`] (same kind, `≡N`-canonical channel/message, and
/// `≡`-canonical residual/abstraction) are collapsed to one. The retained
/// representative keeps its **nominal** residual so it can still be stepped.
/// This is the accessor downstream consumers (e.g. labelled bisimulation)
/// should prefer when duplicate parallel components would otherwise inflate the
/// edge set; on the `τ` fragment it yields exactly
/// [`step_labeled`](crate::reduce::step_labeled)'s deduplicated steps.
pub fn canonical_transitions(p: &Proc) -> Vec<Transition> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for t in transitions(p) {
        if seen.insert(canonical_key(&t)) {
            out.push(t);
        }
    }
    out
}

/// Just the `≡`-deduplicated `τ` transitions of `p`.
///
/// The `τ` filter of [`canonical_transitions`]; by construction this is exactly
/// [`step_labeled`](crate::reduce::step_labeled)'s step set, re-presented as
/// [`Transition::Tau`]s.
pub fn canonical_tau_transitions(p: &Proc) -> Vec<Transition> {
    canonical_transitions(p)
        .into_iter()
        .filter(Transition::is_tau)
        .collect()
}
