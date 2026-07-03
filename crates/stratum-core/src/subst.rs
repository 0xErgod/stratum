//! Substitution for the ρ-calculus — the two distinct notions of §2.5 and §2.7.
//!
//! The calculus has *two* substitutions, and conflating them is the classic
//! mistake:
//!
//! * **Syntactic** ([`subst_syntactic`]) is only a device for α-equivalence.
//!   The process body under a quote `⌜R⌝` is **impervious** to it (§2.6): the
//!   "static quote". The lifted body of `x⟨|R|⟩` is *not* impervious — it is
//!   substituted, which is the "dynamic quote".
//! * **Semantic** ([`subst_semantic`]) is the engine of computation used by the
//!   `Comm` rule (§2.8). It agrees with syntactic substitution everywhere
//!   except on drop: `(*x){⌜Q⌝/y} = Q` when `x ≡N y` (§2.7) — dropping the
//!   substituted name *runs* the code it names.
//!
//! Both substitutions replace a bound symbol `y` with a replacement [`Name`].
//! Because binder symbols are globally unique (see [`crate::term::fresh_sym`]),
//! neither performs α-renaming: capture is impossible.

use crate::term::{Name, Proc};

/// Substitute the replacement name for a bound-name occurrence, without
/// entering quote bodies (used for both substitutions on *name* positions).
fn subst_name(n: &Name, y: u64, repl: &Name) -> Name {
    match n {
        // A matching bound occurrence is replaced by the incoming name.
        Name::Var(k) if *k == y => repl.clone(),
        Name::Var(_) => n.clone(),
        // The body under a quote is impervious to substitution (§2.6).
        Name::Quote(_) => n.clone(),
    }
}

/// Syntactic substitution `P{repl/y}` (§2.5): the substitution used by
/// α-equivalence.
///
/// Note the asymmetry that defines dynamic vs. static quoting: the lifted body
/// of [`Proc::Lift`] is descended into, but the body under a [`Name::Quote`]
/// (reached via [`subst_name`]) is not.
pub fn subst_syntactic(p: &Proc, y: u64, repl: &Name) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => Proc::Drop(subst_name(n, y, repl)),
        Proc::Lift { chan, arg } => Proc::Lift {
            chan: subst_name(chan, y, repl),
            arg: Box::new(subst_syntactic(arg, y, repl)),
        },
        Proc::Input { chan, bound, body } => Proc::Input {
            chan: subst_name(chan, y, repl),
            bound: *bound,
            body: Box::new(subst_syntactic(body, y, repl)),
        },
        Proc::Par(ps) => Proc::Par(ps.iter().map(|q| subst_syntactic(q, y, repl)).collect()),
    }
}

/// Semantic substitution `P{repl/y}` (§2.7): the engine of computation.
///
/// Identical to [`subst_syntactic`] except on drop. If the dropped name is the
/// one being substituted and `repl` is a quote `⌜Q⌝`, the whole `*y` process is
/// replaced by `Q` — the dropped name is run. If `repl` is itself a bound name,
/// `*y` becomes a drop of that name.
pub fn subst_semantic(p: &Proc, y: u64, repl: &Name) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => match n {
            Name::Var(k) if *k == y => match repl {
                // Drop of the substituted name: run the quoted code (§2.7).
                Name::Quote(q) => (**q).clone(),
                // Substituted name is not (yet) a quote: remain a drop of it.
                Name::Var(_) => Proc::Drop(repl.clone()),
            },
            _ => Proc::Drop(subst_name(n, y, repl)),
        },
        Proc::Lift { chan, arg } => Proc::Lift {
            chan: subst_name(chan, y, repl),
            arg: Box::new(subst_semantic(arg, y, repl)),
        },
        Proc::Input { chan, bound, body } => Proc::Input {
            chan: subst_name(chan, y, repl),
            bound: *bound,
            body: Box::new(subst_semantic(body, y, repl)),
        },
        Proc::Par(ps) => Proc::Par(ps.iter().map(|q| subst_semantic(q, y, repl)).collect()),
    }
}
