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
    go_proc(p, &mut env, &mut counter)
}

/// Render a process, threading the binder environment and the fresh-id counter.
fn go_proc(p: &Proc, env: &mut Vec<(u64, String)>, counter: &mut usize) -> String {
    match p {
        Proc::Zero => "0".to_string(),
        Proc::Drop(name) => format!("*{}", go_name(name, env, counter)),
        Proc::Lift { chan, arg } => {
            format!(
                "{}!({})",
                go_name(chan, env, counter),
                go_proc(arg, env, counter)
            )
        }
        Proc::Input { chan, bound, body } => {
            // The channel is resolved in the outer scope, before the binder.
            let chan_s = go_name(chan, env, counter);
            let id = format!("v{counter}");
            *counter += 1;
            env.push((*bound, id.clone()));
            let body_s = go_proc(body, env, counter);
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
                .map(|c| go_proc(c, env, counter))
                .collect::<Vec<_>>()
                .join(" | ")
        }
    }
}

/// Render a name, quoting a compound process body in parentheses.
fn go_name(name: &Name, env: &mut Vec<(u64, String)>, counter: &mut usize) -> String {
    match name {
        Name::Var(sym) => env
            .iter()
            .rev()
            .find(|(s, _)| s == sym)
            .map(|(_, id)| id.clone())
            .expect("closed term: every Var resolves to an enclosing binder"),
        Name::Quote(p) => match &**p {
            Proc::Zero => "@0".to_string(),
            other => format!("@({})", go_proc(other, env, counter)),
        },
    }
}
