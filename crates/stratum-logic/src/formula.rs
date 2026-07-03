//! Syntax of the modal μ-calculus, in positive normal form.
//!
//! Formulas are kept in positive normal form — negation appears only on atomic
//! propositions ([`Formula::NotProp`]) — so every fixpoint variable occurs under
//! an even number of negations and the semantic functional is monotone. This is
//! what makes the fixpoint iteration in [`crate::check`] well-defined and
//! terminating. Use [`neg`] to negate a *closed* formula; it returns the dual in
//! positive normal form.
//!
//! The μ-calculus subsumes LTL and CTL; the [`ef`], [`ag`], [`af`], [`eg`],
//! [`ex`] helpers give the usual CTL operators as derived fixpoints.

use std::sync::atomic::{AtomicUsize, Ordering};

use stratum_core::{name_equiv, Name};

/// Which transitions a modality ranges over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Action {
    /// Any transition, regardless of channel.
    Any,
    /// Only transitions whose firing channel is `≡N` to this name.
    On(Name),
}

impl Action {
    /// Whether a transition with the given (canonical) channel label is in range.
    pub fn matches(&self, label: &Name) -> bool {
        match self {
            Action::Any => true,
            Action::On(n) => name_equiv(n, label),
        }
    }
}

/// Boxed subformula.
type Bf = Box<Formula>;

/// A modal μ-calculus formula (positive normal form).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    /// `⊤` — holds everywhere.
    True,
    /// `⊥` — holds nowhere.
    False,
    /// An atomic proposition, evaluated per state by the checker's labelling.
    Prop(String),
    /// The negation of an atomic proposition.
    NotProp(String),
    /// `φ ∧ ψ`.
    And(Bf, Bf),
    /// `φ ∨ ψ`.
    Or(Bf, Bf),
    /// `⟨a⟩φ` — some `a`-transition reaches a state satisfying `φ`.
    Diamond(Action, Bf),
    /// `[a]φ` — every `a`-transition reaches a state satisfying `φ`.
    Box(Action, Bf),
    /// `μX.φ` — least fixpoint.
    Mu(String, Bf),
    /// `νX.φ` — greatest fixpoint.
    Nu(String, Bf),
    /// A fixpoint variable.
    Var(String),
    /// `K_A φ` — agent `A` *knows* `φ`: `φ` holds in every state `A` cannot
    /// distinguish from the current one (universal over `A`'s information field).
    Knows(String, Bf),
    /// `P_A φ` — agent `A` considers `φ` *possible*: `φ` holds in some state `A`
    /// cannot distinguish from the current one. The epistemic dual of `Knows`.
    Possible(String, Bf),
}

/// `⊤`.
pub fn tt() -> Formula {
    Formula::True
}
/// `⊥`.
pub fn ff() -> Formula {
    Formula::False
}
/// Atomic proposition `p`.
pub fn prop(p: &str) -> Formula {
    Formula::Prop(p.to_string())
}
/// `φ ∧ ψ`.
pub fn and(a: Formula, b: Formula) -> Formula {
    Formula::And(Box::new(a), Box::new(b))
}
/// `φ ∨ ψ`.
pub fn or(a: Formula, b: Formula) -> Formula {
    Formula::Or(Box::new(a), Box::new(b))
}
/// `⟨a⟩φ`.
pub fn diamond(a: Action, f: Formula) -> Formula {
    Formula::Diamond(a, Box::new(f))
}
/// `[a]φ`.
pub fn boxm(a: Action, f: Formula) -> Formula {
    Formula::Box(a, Box::new(f))
}
/// `μX.φ`.
pub fn mu(x: &str, f: Formula) -> Formula {
    Formula::Mu(x.to_string(), Box::new(f))
}
/// `νX.φ`.
pub fn nu(x: &str, f: Formula) -> Formula {
    Formula::Nu(x.to_string(), Box::new(f))
}
/// Fixpoint variable `X`.
pub fn var(x: &str) -> Formula {
    Formula::Var(x.to_string())
}

/// Negate a **closed** formula, returning its positive-normal-form dual.
///
/// De Morgan on the connectives, `⟨⟩ ↔ []`, `μ ↔ ν`, `⊤ ↔ ⊥`, `Prop ↔ NotProp`.
/// Fixpoint variables are left intact: dualizing a closed formula keeps every
/// variable occurrence positive.
pub fn neg(f: Formula) -> Formula {
    match f {
        Formula::True => Formula::False,
        Formula::False => Formula::True,
        Formula::Prop(p) => Formula::NotProp(p),
        Formula::NotProp(p) => Formula::Prop(p),
        Formula::And(a, b) => Formula::Or(Box::new(neg(*a)), Box::new(neg(*b))),
        Formula::Or(a, b) => Formula::And(Box::new(neg(*a)), Box::new(neg(*b))),
        Formula::Diamond(act, g) => Formula::Box(act, Box::new(neg(*g))),
        Formula::Box(act, g) => Formula::Diamond(act, Box::new(neg(*g))),
        Formula::Mu(x, g) => Formula::Nu(x, Box::new(neg(*g))),
        Formula::Nu(x, g) => Formula::Mu(x, Box::new(neg(*g))),
        Formula::Var(x) => Formula::Var(x),
        Formula::Knows(a, g) => Formula::Possible(a, Box::new(neg(*g))),
        Formula::Possible(a, g) => Formula::Knows(a, Box::new(neg(*g))),
    }
}

static FRESH: AtomicUsize = AtomicUsize::new(0);

fn fresh_var() -> String {
    format!("_X{}", FRESH.fetch_add(1, Ordering::Relaxed))
}

/// `EX φ = ⟨Any⟩φ` — some successor satisfies `φ`.
pub fn ex(f: Formula) -> Formula {
    diamond(Action::Any, f)
}

/// `EF φ = μX. φ ∨ ⟨Any⟩X` — some path eventually reaches `φ`.
pub fn ef(f: Formula) -> Formula {
    let x = fresh_var();
    mu(&x, or(f, diamond(Action::Any, var(&x))))
}

/// `AG φ = νX. φ ∧ [Any]X` — `φ` holds on all reachable states.
pub fn ag(f: Formula) -> Formula {
    let x = fresh_var();
    nu(&x, and(f, boxm(Action::Any, var(&x))))
}

/// `EG φ = νX. φ ∧ ⟨Any⟩X` — some *infinite* path keeps `φ` (a deadlock cannot
/// satisfy the inner `⟨⟩`, so it does not count).
pub fn eg(f: Formula) -> Formula {
    let x = fresh_var();
    nu(&x, and(f, diamond(Action::Any, var(&x))))
}

/// `AF φ = μX. φ ∨ ([Any]X ∧ ⟨Any⟩⊤)` — on all paths `φ` eventually holds.
///
/// The `⟨Any⟩⊤` conjunct makes this deadlock-aware: a maximal finite path that
/// terminates without `φ` correctly falsifies `AF φ` (unlike the total-relation
/// encoding `μX. φ ∨ [Any]X`).
pub fn af(f: Formula) -> Formula {
    let x = fresh_var();
    mu(
        &x,
        or(
            f,
            and(boxm(Action::Any, var(&x)), diamond(Action::Any, tt())),
        ),
    )
}

/// `⟨c⟩⊤` — a transition on channel `c` is possible now.
pub fn can(channel: Name) -> Formula {
    diamond(Action::On(channel), tt())
}

/// `K_A φ` — agent `A` knows `φ`.
pub fn knows(agent: &str, f: Formula) -> Formula {
    Formula::Knows(agent.to_string(), Box::new(f))
}

/// `P_A φ` — agent `A` considers `φ` possible.
pub fn possible(agent: &str, f: Formula) -> Formula {
    Formula::Possible(agent.to_string(), Box::new(f))
}
