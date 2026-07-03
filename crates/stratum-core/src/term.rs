//! The term language of the reflective higher-order (ρ) calculus.
//!
//! This follows Meredith & Radestock, *A Reflective Higher-order Calculus*
//! (ENTCS 141(5), 2005), §2.0.1:
//!
//! ```text
//! P, Q ::= 0              null process
//!        | x(y).P         input   (binds the name y)
//!        | x⟨|P|⟩          lift    (asynchronous output; no continuation)
//!        | *x             drop    (dereference / unquote)
//!        | P | Q          parallel
//! x, y  ::= ⌜P⌝            name = quoted process   (the ONLY name former)
//! ```
//!
//! The distinguishing feature of the calculus is that **names are quoted
//! processes** — there are no atomic names (§2.0.2). Input prefixes bind names;
//! we represent a bound name with a globally-unique symbol allocated by
//! [`fresh_sym`]. Because every binder gets a fresh symbol, substitution never
//! captures, so no on-the-fly α-renaming is required (see [`crate::subst`]).
//! α-equivalence is instead recovered at comparison time by
//! [`crate::congruence::canonicalize`], which re-labels bound symbols as de
//! Bruijn indices.

use std::collections::BTreeSet;
use std::sync::atomic::{AtomicU64, Ordering};

/// Monotonic source of fresh binder symbols.
static FRESH: AtomicU64 = AtomicU64::new(1);

/// Allocate a globally-unique symbol for a fresh input-bound name.
///
/// Uniqueness is what lets [`crate::subst`] avoid variable capture without
/// α-renaming: no two binders ever share a symbol, so a free symbol in a
/// substituted name can never be recaptured by a binder we recurse under.
pub fn fresh_sym() -> u64 {
    FRESH.fetch_add(1, Ordering::Relaxed)
}

/// A name of the ρ-calculus.
///
/// Per §2.0.1 the only name former is the quote `⌜P⌝` of a process. The
/// [`Name::Var`] case is not part of the surface grammar; it stands for a name
/// *bound* by an enclosing [`Proc::Input`] and is eliminated (turned into a de
/// Bruijn index) by canonicalization.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Name {
    /// `⌜P⌝` — the quote of a process. A name *is* the code of a process.
    Quote(Box<Proc>),
    /// A bound-name occurrence. In a nominal term this carries the binder's
    /// [`fresh_sym`]; in a canonical term it carries a de Bruijn index.
    Var(u64),
}

/// A process of the ρ-calculus.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Proc {
    /// `0` — the null process; the sole atom from which all else is built
    /// (§2.0.6, §2.1).
    Zero,
    /// `x(y).P` — input on channel `chan`, binding the name `bound` in `body`.
    Input {
        /// The channel name `x`.
        chan: Name,
        /// The symbol introduced by this binder (nominal) or `0` (canonical).
        bound: u64,
        /// The continuation `P`, in whose scope `bound` is visible.
        body: Box<Proc>,
    },
    /// `x⟨|P|⟩` — asynchronous lift/output. Unlike a quoted name, the lifted
    /// process `arg` **is** subject to substitution (the "dynamic quote" of
    /// §2.6).
    Lift {
        /// The channel name `x`.
        chan: Name,
        /// The lifted process `P`, which will be reified to the name `⌜P⌝` on
        /// receipt.
        arg: Box<Proc>,
    },
    /// `*x` — drop/dereference. Inert except under substitution (§2.0.4): a
    /// dropped name only "runs" once a quoted process is substituted for it.
    Drop(Name),
    /// `P | Q` — parallel composition. Stored as a vector and treated as an
    /// associative–commutative multiset with unit `0` by canonicalization
    /// (§2.3).
    Par(Vec<Proc>),
}

/// `0` — the null process.
pub fn zero() -> Proc {
    Proc::Zero
}

/// `⌜P⌝` — the quote of a process, as a name.
pub fn quote(p: Proc) -> Name {
    Name::Quote(Box::new(p))
}

/// `*x` — the drop of a name.
///
/// Named `drop_` to avoid shadowing [`std::mem::drop`].
pub fn drop_(name: Name) -> Proc {
    Proc::Drop(name)
}

/// `x⟨|P|⟩` — lift `arg` on channel `chan`.
pub fn lift(chan: Name, arg: Proc) -> Proc {
    Proc::Lift {
        chan,
        arg: Box::new(arg),
    }
}

/// `P | Q | ...` — parallel composition of the given processes.
pub fn par(procs: impl IntoIterator<Item = Proc>) -> Proc {
    Proc::Par(procs.into_iter().collect())
}

/// Output sugar `x[y] ≜ x⟨|*y|⟩` (§2.0.5): send the *name* `y` on channel `x`.
///
/// On receipt the object `⌜*y⌝ ≡N y`, so this delivers the name `y` itself.
pub fn output(chan: Name, name: Name) -> Proc {
    lift(chan, drop_(name))
}

/// `x(y).P` — build an input, supplying the freshly-bound name to `body`.
///
/// The closure receives the bound name as a [`Name::Var`] so it can be used
/// inside the continuation, e.g. `input(ch, |y| drop_(y))` builds `x(y).*y`.
pub fn input(chan: Name, body: impl FnOnce(Name) -> Proc) -> Proc {
    let sym = fresh_sym();
    let body = body(Name::Var(sym));
    Proc::Input {
        chan,
        bound: sym,
        body: Box::new(body),
    }
}

impl Proc {
    /// The free bound-name variables of a process.
    ///
    /// This is the well-formedness witness: a term is *closed* — a genuine
    /// term of the calculus rather than an open fragment — exactly when this is
    /// empty (see [`Proc::is_closed`]). It descends through quotes, matching the
    /// scoping used by [`crate::congruence`], so a variable that only refers to
    /// an enclosing input from *inside* a quote still counts as bound.
    pub fn free_vars(&self) -> BTreeSet<u64> {
        let mut bound = Vec::new();
        let mut out = BTreeSet::new();
        self.collect_free(&mut bound, &mut out);
        out
    }

    /// Whether the process is closed (has no free bound-name variables).
    ///
    /// Reduction preserves this invariant; the test suite checks it.
    pub fn is_closed(&self) -> bool {
        self.free_vars().is_empty()
    }

    fn collect_free(&self, bound: &mut Vec<u64>, out: &mut BTreeSet<u64>) {
        match self {
            Proc::Zero => {}
            Proc::Drop(n) => n.collect_free(bound, out),
            Proc::Lift { chan, arg } => {
                chan.collect_free(bound, out);
                arg.collect_free(bound, out);
            }
            Proc::Input { chan, bound: b, body } => {
                // The channel is in scope before the input binds its name.
                chan.collect_free(bound, out);
                bound.push(*b);
                body.collect_free(bound, out);
                bound.pop();
            }
            Proc::Par(ps) => {
                for p in ps {
                    p.collect_free(bound, out);
                }
            }
        }
    }
}

impl Name {
    fn collect_free(&self, bound: &mut Vec<u64>, out: &mut BTreeSet<u64>) {
        match self {
            Name::Var(s) => {
                if !bound.contains(s) {
                    out.insert(*s);
                }
            }
            Name::Quote(p) => p.collect_free(bound, out),
        }
    }

    /// Quote depth `#(x)` (§2.5): `#(⌜P⌝) = 1 + #(P)`, and a bound-name
    /// occurrence carries no quotes.
    ///
    /// The grammar's strict alternation between quotes and process constructors
    /// makes this finite, which is exactly what makes name equivalence `≡N`
    /// (and hence `≡`, `≡α`) terminate.
    pub fn quote_depth(&self) -> usize {
        match self {
            Name::Var(_) => 0,
            Name::Quote(p) => 1 + p.quote_depth(),
        }
    }
}

impl Proc {
    /// Quote depth `#(P)` (§2.5): the maximum quote depth over the names
    /// occurring in `P`, or `0` if none occur.
    pub fn quote_depth(&self) -> usize {
        match self {
            Proc::Zero => 0,
            Proc::Input { chan, body, .. } => chan.quote_depth().max(body.quote_depth()),
            Proc::Lift { chan, arg } => chan.quote_depth().max(arg.quote_depth()),
            Proc::Drop(n) => n.quote_depth(),
            Proc::Par(ps) => ps.iter().map(Proc::quote_depth).max().unwrap_or(0),
        }
    }
}
