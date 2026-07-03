//! The renderer: a [`stratum_core::Proc`] → valid raw surface syntax.
//!
//! This is the inverse direction of [`crate::parse`] and the engine behind
//! [`crate::expand`]. It emits the fully-desugared term — every quote explicit,
//! correctly parenthesized — using no `def`/`new`/macro sugar, so its output is
//! always re-parseable and, up to structural congruence, round-trips:
//! `parse(to_source(p)) ≡ p` for every closed `p`.
//!
//! Input binders are named `v0, v1, …` in the order they are visited, and each
//! bound-name occurrence is rendered against the innermost enclosing binder.

use stratum_core::term::{Name, Proc};

use crate::Aliases;

/// Render a closed [`Proc`] back to raw surface syntax.
///
/// The result parses (with [`crate::parse`]) to a term structurally congruent to
/// `p`. The term must be closed — every [`Name::Var`] must refer to an enclosing
/// [`Proc::Input`], which is exactly the class the surface syntax can express;
/// this always holds for the output of [`crate::parse`].
///
/// ```
/// use stratum_syntax::{parse, to_source};
/// use stratum_core::structurally_congruent;
///
/// let p = parse("@0!(0) | @0(y).*y").unwrap();
/// let src = to_source(&p);
/// assert!(structurally_congruent(&parse(&src).unwrap(), &p));
/// ```
pub fn to_source(p: &Proc) -> String {
    let mut env: Vec<(u64, String)> = Vec::new();
    let mut counter = 0usize;
    go_proc(p, &mut env, &mut counter, None)
}

/// Render a closed [`Proc`] back to surface syntax, **folding known names to
/// their source aliases**.
///
/// This is the readable/backward complement of [`to_source`]: it is identical
/// except that wherever a name's canonical form is a key of `aliases` — a
/// top-level `new` name or a name-shaped `def` alias captured by
/// [`crate::parse_with_aliases`] — the source identifier is printed in place of
/// the explicit `@…` quote. Names with no alias fall back to the raw quote, and
/// everything else (binders `v0, v1, …`, structure, parenthesization) matches
/// [`to_source`] exactly.
///
/// The output is for **reading, not re-parsing**: because it drops the
/// `def`/`new` preamble that would introduce those identifiers, feeding it back
/// to [`crate::parse`] generally fails on the now-unbound aliases. Use
/// [`to_source`] (the `--raw` form) when a re-parseable term is required.
///
/// ```
/// use stratum_syntax::{parse_with_aliases, to_source, to_source_folded};
///
/// let (p, aliases) = parse_with_aliases("new req, ack\nreq!(0) | req(x).ack!(0)").unwrap();
/// assert_eq!(to_source_folded(&p, &aliases), "req!(0) | req(v0).ack!(0)");
/// // The raw view spells the ground names out in full.
/// assert_eq!(to_source(&p), "@0!(0) | @0(v0).@(@0!(0))!(0)");
/// ```
pub fn to_source_folded(p: &Proc, aliases: &Aliases) -> String {
    let mut env: Vec<(u64, String)> = Vec::new();
    let mut counter = 0usize;
    go_proc(p, &mut env, &mut counter, Some(aliases))
}

/// Render a process, threading the binder environment, the fresh-id counter, and
/// (when folding) the alias dictionary.
fn go_proc(
    p: &Proc,
    env: &mut Vec<(u64, String)>,
    counter: &mut usize,
    aliases: Option<&Aliases>,
) -> String {
    match p {
        Proc::Zero => "0".to_string(),
        Proc::Drop(name) => format!("*{}", go_name(name, env, counter, aliases)),
        Proc::Lift { chan, arg } => {
            format!(
                "{}!({})",
                go_name(chan, env, counter, aliases),
                go_proc(arg, env, counter, aliases)
            )
        }
        Proc::Input { chan, bound, body } => {
            // The channel is resolved in the outer scope, before the binder.
            let chan_s = go_name(chan, env, counter, aliases);
            let id = format!("v{counter}");
            *counter += 1;
            env.push((*bound, id.clone()));
            let body_s = go_proc(body, env, counter, aliases);
            env.pop();
            // The continuation is a single term; a parallel body must be grouped.
            let body_s = if matches!(**body, Proc::Par(_)) {
                format!("({body_s})")
            } else {
                body_s
            };
            format!("{chan_s}({id}).{body_s}")
        }
        Proc::Par(ps) => {
            if ps.is_empty() {
                // The empty parallel product is the unit `0`.
                return "0".to_string();
            }
            ps.iter()
                .map(|c| go_proc(c, env, counter, aliases))
                .collect::<Vec<_>>()
                .join(" | ")
        }
    }
}

/// Render a name, quoting a compound process body in parentheses.
///
/// When `aliases` is present, a name whose canonical form is a known alias is
/// printed as the source identifier instead of its `@…` quote.
fn go_name(
    name: &Name,
    env: &mut Vec<(u64, String)>,
    counter: &mut usize,
    aliases: Option<&Aliases>,
) -> String {
    if let Some(aliases) = aliases {
        if let Some(id) = aliases.get(name) {
            return id.to_string();
        }
    }
    match name {
        Name::Var(sym) => env
            .iter()
            .rev()
            .find(|(s, _)| s == sym)
            .map(|(_, id)| id.clone())
            .expect("closed term: every Var resolves to an enclosing binder"),
        Name::Quote(p) => match &**p {
            Proc::Zero => "@0".to_string(),
            other => format!("@({})", go_proc(other, env, counter, aliases)),
        },
    }
}
