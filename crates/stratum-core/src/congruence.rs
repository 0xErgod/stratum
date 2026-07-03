//! Structural congruence `≡` and name equivalence `≡N` (§2.3, §2.4).
//!
//! Both are decided by reducing a term to a **canonical form** and comparing
//! for syntactic equality. The canonical form quotients by exactly the laws the
//! paper gives:
//!
//! * **α-equivalence** (part of `≡`): bound symbols are re-labelled as de Bruijn
//!   indices, so the choice of binder symbol is forgotten.
//! * **Parallel is an abelian monoid** (§2.3): `Par` is flattened, units `0` are
//!   dropped, and the remaining components are sorted into a canonical order.
//! * **Quote-drop** (`≡N`, §2.4): `⌜*x⌝ ≡N x`.
//! * **Struct-equiv** (`≡N`, §2.4): `⌜P⌝ ≡N ⌜Q⌝` whenever `P ≡ Q`, obtained
//!   here by canonicalizing under the quote.
//!
//! The mutual recursion between `≡`, `≡α`, `≡N`, and substitution terminates
//! because each descent under a quote strictly decreases quote depth (§2.5);
//! that induction is mirrored by the structural recursion below.
//!
//! Note that quote-drop is a *name*-level law. The process `*⌜P⌝` is **not**
//! structurally congruent to `P` — drop is inert until substitution (§2.0.4) —
//! so [`canon_proc`] never rewrites `Drop(Quote(_))`, while [`canon_name`] does
//! rewrite `Quote(Drop(_))`.

use crate::term::{Name, Proc};

/// Reduce a process to its canonical representative modulo `≡`.
///
/// Two processes are structurally congruent iff their canonical forms are
/// equal; see [`structurally_congruent`].
pub fn canonicalize(p: &Proc) -> Proc {
    let mut env = Vec::new();
    canon_proc(p, &mut env)
}

/// `P ≡ Q` — structural congruence (§2.3).
pub fn structurally_congruent(a: &Proc, b: &Proc) -> bool {
    canonicalize(a) == canonicalize(b)
}

/// `m ≡N n` — name equivalence (§2.4).
pub fn name_equiv(m: &Name, n: &Name) -> bool {
    let mut em = Vec::new();
    let mut en = Vec::new();
    canon_name(m, &mut em) == canon_name(n, &mut en)
}

/// Reduce a name to its canonical representative modulo `≡N` (§2.4).
///
/// Used to label transitions by their firing channel: two `≡N`-equal channels
/// yield the same label.
pub fn canonicalize_name(n: &Name) -> Name {
    let mut env = Vec::new();
    canon_name(n, &mut env)
}

/// `env` is the stack of enclosing binder symbols, innermost last. A bound
/// occurrence is canonicalized to its de Bruijn index (distance from the top).
fn canon_proc(p: &Proc, env: &mut Vec<u64>) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => Proc::Drop(canon_name(n, env)),
        Proc::Lift { chan, arg } => Proc::Lift {
            // The channel is resolved in the outer scope (before this term's
            // own binder, if any) — Lift introduces no binder, so `env` is
            // already correct here.
            chan: canon_name(chan, env),
            arg: Box::new(canon_proc(arg, env)),
        },
        Proc::Input { chan, bound, body } => {
            // The channel is in scope *before* the input binds its name.
            let chan = canon_name(chan, env);
            env.push(*bound);
            let body = Box::new(canon_proc(body, env));
            env.pop();
            Proc::Input {
                chan,
                bound: 0, // canonical: binder symbol is forgotten
                body,
            }
        }
        Proc::Par(ps) => {
            let mut items = Vec::new();
            for child in ps {
                flatten_into(child, env, &mut items);
            }
            items.sort();
            match items.len() {
                0 => Proc::Zero,           // empty parallel is the unit
                1 => items.pop().unwrap(), // singleton parallel collapses
                _ => Proc::Par(items),
            }
        }
    }
}

/// Canonicalize a parallel component and splice it into `out`, applying the
/// monoid laws: units vanish and nested parallels are flattened.
fn flatten_into(p: &Proc, env: &mut Vec<u64>, out: &mut Vec<Proc>) {
    match canon_proc(p, env) {
        Proc::Zero => {}
        Proc::Par(items) => out.extend(items),
        other => out.push(other),
    }
}

fn canon_name(n: &Name, env: &mut Vec<u64>) -> Name {
    match n {
        Name::Var(sym) => match env.iter().rev().position(|s| s == sym) {
            // de Bruijn index: distance from the innermost binder.
            Some(i) => Name::Var(i as u64),
            // Free occurrence (not expected in closed terms): keep as-is,
            // offset above any plausible de Bruijn index to avoid aliasing a
            // bound occurrence.
            None => Name::Var(u64::MAX - sym),
        },
        Name::Quote(p) => {
            // Struct-equiv: ⌜P⌝ ≡N ⌜Q⌝ iff P ≡ Q — canonicalize under the quote
            // first, so quote-drop is applied up to `≡` (a body that only
            // reduces to `*x` after canonicalization must still collapse).
            match canon_proc(p, env) {
                // Quote-drop: ⌜*x⌝ ≡N x (§2.4). `inner` is already canonical.
                Proc::Drop(inner) => inner,
                other => Name::Quote(Box::new(other)),
            }
        }
    }
}
