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
/// // The raw view spells the ground names out in full. `@0` is reserved, so
/// // req = ground(1) = @(@0!(0)) and ack = ground(2) = @(@0!(@0!(0))).
/// assert_eq!(to_source(&p), "@(@0!(0))!(0) | @(@0!(0))(v0).@(@0!(@0!(0)))!(0)");
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
        // A bound variable resolves to its enclosing input binder; a Var with no
        // binder in scope (e.g. a canonical/de-Bruijn LTS state, or an open term)
        // falls back to `v{sym}` rather than panicking — a total renderer.
        Name::Var(sym) => env
            .iter()
            .rev()
            .find(|(s, _)| s == sym)
            .map(|(_, id)| id.clone())
            .unwrap_or_else(|| format!("v{sym}")),
        Name::Quote(p) => match &**p {
            Proc::Zero => "@0".to_string(),
            other => format!("@({})", go_proc(other, env, counter, aliases)),
        },
    }
}

// ---------------------------------------------------------------------------
// LaTeX rendering (classic reflective rho-calculus notation)
// ---------------------------------------------------------------------------

/// Render a closed [`Proc`] as a LaTeX math expression in the notation of
/// Meredith & Radestock, *A Reflective Higher-order Calculus* (ENTCS 141(5),
/// 2005), §2.0.1: `0` (null), `x(y).P` (input), `x⟨|P|⟩` — the *lift* brackets —
/// for output, `⌝x⌜` (reversed corners) for *drop*, `⌜P⌝` for *quote*, and
/// `P | Q` for parallel composition. Bound names are the paper's single letters
/// `x, y, z, …`, and the name-output sugar `x⟨|⌝y⌜|⟩` is contracted to `x[y]`
/// (§2.0.5).
///
/// The result is bare math (no `$…$` delimiters) intended to be embedded in a
/// `text/latex` MIME payload. It is for reading, not re-parsing.
///
/// ```
/// use stratum_syntax::{parse, to_latex};
///
/// assert_eq!(to_latex(&parse("@0!(0)").unwrap()), r"\ulcorner 0 \urcorner\langle\!| 0 |\!\rangle");
/// // Single-letter binder `x`, and the name-output sugar `x[y]`.
/// assert_eq!(
///     to_latex(&parse("@0(x).@0!(*x)").unwrap()),
///     r"\ulcorner 0 \urcorner(x).\ulcorner 0 \urcorner[x]",
/// );
/// ```
pub fn to_latex(p: &Proc) -> String {
    let mut env: Vec<(u64, String)> = Vec::new();
    let mut counter = 0usize;
    latex_proc(p, &mut env, &mut counter, None)
}

/// Render a closed [`Proc`] as LaTeX, **folding known names to their source
/// aliases** (typeset with `\mathit{…}`). The alias-folding complement of
/// [`to_latex`], analogous to [`to_source_folded`].
///
/// ```
/// use stratum_syntax::{parse_with_aliases, to_latex_folded};
///
/// let (p, aliases) = parse_with_aliases("new req, ack\nreq!(0) | req(x).ack!(0)").unwrap();
/// assert_eq!(
///     to_latex_folded(&p, &aliases),
///     r"\mathit{req}\langle\!| 0 |\!\rangle \mid \mathit{req}(x).\mathit{ack}\langle\!| 0 |\!\rangle",
/// );
/// ```
pub fn to_latex_folded(p: &Proc, aliases: &Aliases) -> String {
    let mut env: Vec<(u64, String)> = Vec::new();
    let mut counter = 0usize;
    latex_proc(p, &mut env, &mut counter, Some(aliases))
}

/// Render a process to LaTeX, threading the binder environment, the fresh-id
/// counter (binders become `v_{0}, v_{1}, …`), and the optional alias table.
fn latex_proc(
    p: &Proc,
    env: &mut Vec<(u64, String)>,
    counter: &mut usize,
    aliases: Option<&Aliases>,
) -> String {
    match p {
        // Meredith–Radestock §2.0.1: `0`, `⌝x⌜` (drop), `x⟨|P|⟩` (lift/output).
        Proc::Zero => "0".to_string(),
        Proc::Drop(name) => {
            format!(
                r"\urcorner {} \ulcorner",
                latex_name(name, env, counter, aliases)
            )
        }
        Proc::Lift { chan, arg } => {
            let chan_s = latex_name(chan, env, counter, aliases);
            match &**arg {
                // Name-output sugar: `x⟨|⌝y⌜|⟩ ≜ x[y]` (Meredith–Radestock §2.0.5).
                Proc::Drop(name) => {
                    format!("{chan_s}[{}]", latex_name(name, env, counter, aliases))
                }
                other => format!(
                    r"{chan_s}\langle\!| {} |\!\rangle",
                    latex_proc(other, env, counter, aliases),
                ),
            }
        }
        Proc::Input { chan, bound, body } => {
            let chan_s = latex_name(chan, env, counter, aliases);
            let id = latex_binder(*counter);
            *counter += 1;
            env.push((*bound, id.clone()));
            let body_s = latex_proc(body, env, counter, aliases);
            env.pop();
            let body_s = if matches!(**body, Proc::Par(_)) {
                format!(r"\left( {body_s} \right)")
            } else {
                body_s
            };
            format!("{chan_s}({id}).{body_s}")
        }
        Proc::Par(ps) => {
            if ps.is_empty() {
                return "0".to_string();
            }
            ps.iter()
                .map(|c| latex_proc(c, env, counter, aliases))
                .collect::<Vec<_>>()
                .join(r" \mid ")
        }
    }
}

/// Render a name to LaTeX: a bound variable as `v_{n}`, a quote as `\ulcorner
/// P\urcorner`, or (when folding) a known alias as `\mathit{name}`.
fn latex_name(
    name: &Name,
    env: &mut Vec<(u64, String)>,
    counter: &mut usize,
    aliases: Option<&Aliases>,
) -> String {
    if let Some(aliases) = aliases {
        if let Some(id) = aliases.get(name) {
            return latex_ident(id);
        }
    }
    match name {
        // Total, like `go_name`: an unresolved Var (canonical/open term) renders
        // as `v_{sym}` instead of panicking.
        Name::Var(sym) => env
            .iter()
            .rev()
            .find(|(s, _)| s == sym)
            .map(|(_, id)| id.clone())
            .unwrap_or_else(|| format!("v_{{{sym}}}")),
        Name::Quote(p) => {
            format!(
                r"\ulcorner {} \urcorner",
                latex_proc(p, env, counter, aliases)
            )
        }
    }
}

/// Render a single [`Name`] to LaTeX, folding a known alias to `\mathit{name}`.
///
/// Standalone (no binder environment), for labelling contexts like LTS
/// transition channels. A bound [`Name::Var`] — which should not appear at the
/// top level — degrades to `v_{sym}` rather than panicking.
pub fn name_to_latex(name: &Name, aliases: Option<&Aliases>) -> String {
    if let Some(aliases) = aliases {
        if let Some(id) = aliases.get(name) {
            return latex_ident(id);
        }
    }
    match name {
        Name::Var(sym) => format!("v_{{{sym}}}"),
        Name::Quote(_) => {
            let mut env: Vec<(u64, String)> = Vec::new();
            let mut counter = 0usize;
            latex_name(name, &mut env, &mut counter, aliases)
        }
    }
}

/// The LaTeX name for the `n`-th input binder, following the paper's single
/// letters `x, y, z, …` (§2 uses `x, y, z` for names). After the pool is
/// exhausted it wraps with a numeric subscript (`x_{1}`, `y_{1}`, …) so binders
/// stay distinct in arbitrarily large terms.
fn latex_binder(n: usize) -> String {
    const LETTERS: &[u8] = b"xyzuvwpqrst";
    let base = LETTERS[n % LETTERS.len()] as char;
    let tier = n / LETTERS.len();
    if tier == 0 {
        base.to_string()
    } else {
        format!("{base}_{{{tier}}}")
    }
}

/// Typeset a source identifier as an upright multi-letter math name,
/// `\mathit{…}`, escaping the LaTeX-special `_` so channel names like `K_A`
/// survive in math mode.
pub fn latex_ident(id: &str) -> String {
    format!(r"\mathit{{{}}}", id.replace('_', r"\_"))
}
