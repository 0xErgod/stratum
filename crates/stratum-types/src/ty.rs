//! The **type language** and the **sort context** Γ.
//!
//! Types here are *spatial / behavioral* types of processes, which — because
//! names are quoted processes — double as the types of names (the type of a name
//! is the type of the process it quotes; see [`crate::check`]).
//!
//! The language is deliberately small, so the discipline is *decidable* and
//! *transparent*:
//!
//! ```text
//! T ::= Nil            the null process 0 (spatially empty)
//!     | Chan(T)        a channel that carries messages of type T
//!     | Proc           an opaque process (top: some process, no guarantee)
//! ```
//!
//! `Nil` is the terminal type reflected by `0`; `Chan(T)` is the type of a name
//! usable as a channel that inputs/outputs messages of type `T`; `Proc` is a
//! top element that keeps synthesis total for payloads the first-cut discipline
//! does not further constrain (e.g. a composite parallel message). Types are
//! compared by ordinary structural equality.

use std::collections::HashMap;
use std::fmt;

use stratum_core::{canonicalize_name, Name};

/// A spatial / behavioral **type** of a process — and hence, reflectively, of a
/// name (the type of the process the name quotes).
///
/// See the [module docs](self) for the grammar.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ty {
    /// `Nil` — the type of the null process `0`; the terminal sort.
    Nil,
    /// `Chan(T)` — the type of a name usable as a **channel** that carries
    /// messages (names) of type `T`.
    Chan(Box<Ty>),
    /// `Proc` — an opaque process. Top of the (flat) type order: it is what
    /// synthesis falls back to for a message shape the first-cut discipline does
    /// not analyse further. A channel is never *silently* given this type, so it
    /// only appears where a payload is genuinely unconstrained.
    Proc,
}

impl Ty {
    /// `Chan(T)` — a channel carrying messages of type `carried`.
    #[must_use]
    pub fn chan(carried: Ty) -> Ty {
        Ty::Chan(Box::new(carried))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Ty::Nil => f.write_str("Nil"),
            Ty::Proc => f.write_str("Proc"),
            Ty::Chan(t) => write!(f, "Chan({t})"),
        }
    }
}

/// A **sort context** Γ: what each *free channel* carries.
///
/// Channels are quoted processes, so keys are [`Name`]s — and, crucially, they
/// are compared **up to name equivalence `≡N`** (§2.4): a channel is identified
/// by the *code* it quotes, not by a surface spelling. Keys are canonicalized on
/// insert and lookup, so `⌜*⌜P⌝⌝` and `⌜P⌝` name the same channel.
///
/// Γ records, for each channel, the type of the **messages it carries** (the `T`
/// of a `Chan(T)`), not the channel's own type. Bound names received on a
/// channel are typed at that carried type by the checker; they do not live in Γ.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Env {
    carried: HashMap<Name, Ty>,
}

impl Env {
    /// An empty sort context.
    #[must_use]
    pub fn new() -> Env {
        Env::default()
    }

    /// Declare that `chan` carries messages of type `carries`.
    ///
    /// The channel key is canonicalized (`≡N`), so re-declaring an
    /// `≡N`-equivalent channel overwrites the earlier entry.
    pub fn declare(&mut self, chan: Name, carries: Ty) -> &mut Env {
        self.carried.insert(canonicalize_name(&chan), carries);
        self
    }

    /// Builder form of [`declare`](Env::declare).
    #[must_use]
    pub fn with(mut self, chan: Name, carries: Ty) -> Env {
        self.declare(chan, carries);
        self
    }

    /// The type of messages carried by `chan`, if declared (looked up `≡N`).
    #[must_use]
    pub fn carried(&self, chan: &Name) -> Option<&Ty> {
        self.carried.get(&canonicalize_name(chan))
    }
}
