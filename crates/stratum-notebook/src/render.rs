//! Rendering: turning toolkit values into [`MimeBundle`]s.
//!
//! Every renderer produces a `text/plain` **ASCII listing** (always — copyable
//! as-is by any front-end). When the session is in [`Repr::Latex`] a renderer
//! *also* emits a `text/latex` payload in classic reflective rho-calculus
//! notation, which a MathJax front-end typesets and which copies as either LaTeX
//! source or an image. Diagrams were dropped in favour of listings, so there is
//! no SVG output and no layout dependency.
//!
//! Nothing here knows about ZeroMQ or Jupyter; the kernel maps the MIME keys
//! onto its own display messages.

use stratum::core::{canonicalize, Name, Proc};
use stratum::equiv::Verdict;
use stratum::logic::Checked;
use stratum::lts::{format_name, Lts};
use stratum::syntax::{
    name_to_latex, to_latex, to_latex_folded, to_source, to_source_folded, Aliases,
};
use stratum::types::TypeError;

use crate::Repr;

/// A rendered cell result as a set of alternative MIME representations.
///
/// `text_plain` is always present (an ASCII listing every front-end can show and
/// the user can copy). `text_latex` is the optional richer alternative, emitted
/// only in [`Repr::Latex`] mode.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MimeBundle {
    /// `text/plain` representation. Always populated.
    pub text_plain: String,
    /// Optional `text/latex` representation (classic rho-calculus notation).
    pub text_latex: Option<String>,
}

impl MimeBundle {
    /// A bundle carrying only `text/plain`.
    #[must_use]
    pub fn plain(text: impl Into<String>) -> Self {
        Self {
            text_plain: text.into(),
            text_latex: None,
        }
    }
}

/// Escape the five XML/HTML metacharacters so arbitrary process source can be
/// embedded in `text/html` safely. (Cell output is HTML-free, but the
/// interactive `inspect` docs still build small HTML snippets.)
#[must_use]
pub fn escape_html(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            _ => out.push(c),
        }
    }
    out
}

/// Wrap a bare math expression as a `text/latex` display-math payload.
pub(crate) fn display_math(inner: &str) -> String {
    format!("$$\n{inner}\n$$")
}

/// Escape the LaTeX-special characters so a toolkit-generated status string is
/// safe inside a `\text{…}` box.
pub(crate) fn escape_latex_text(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str(r"\textbackslash{}"),
            '_' | '&' | '%' | '$' | '#' | '{' | '}' => {
                out.push('\\');
                out.push(c);
            }
            '~' => out.push_str(r"\textasciitilde{}"),
            '^' => out.push_str(r"\textasciicircum{}"),
            _ => out.push(c),
        }
    }
    out
}

/// A `text/latex` payload for a short status line: the text boxed in math mode.
fn latex_status(plain: &str) -> Option<String> {
    Some(display_math(&format!(
        r"\text{{{}}}",
        escape_latex_text(plain)
    )))
}

/// Fold a channel [`Name`] to its source alias for the ASCII LTS listing,
/// falling back to the compact raw form when it has no alias.
fn fold_name_ascii(name: &Name, aliases: &Aliases) -> String {
    aliases
        .get(name)
        .map_or_else(|| format_name(name), str::to_string)
}

/// Render a process as its **surface form** only (the core is available on
/// demand via `#expand`). ASCII plain always; a classic-rho `text/latex` form in
/// LaTeX mode.
#[must_use]
pub fn render_proc(p: &Proc, aliases: &Aliases, repr: Repr) -> MimeBundle {
    MimeBundle {
        text_plain: to_source_folded(p, aliases),
        text_latex: match repr {
            Repr::Ascii => None,
            Repr::Latex => Some(display_math(&to_latex_folded(p, aliases))),
        },
    }
}

/// Render a process's desugared **pure core** (the `#expand` view): raw surface
/// syntax in ASCII, classic-rho `\ulcorner…\urcorner` notation in LaTeX.
#[must_use]
pub fn render_core(p: &Proc, repr: Repr) -> MimeBundle {
    let core = canonicalize(p);
    MimeBundle {
        text_plain: to_source(&core),
        text_latex: match repr {
            Repr::Ascii => None,
            Repr::Latex => Some(display_math(&to_latex(&core))),
        },
    }
}

/// Render an LTS as a **listing**: a state/transition summary plus one line per
/// state (its folded process) and one per transition (`s_i --chan--> s_j`).
#[must_use]
pub fn render_lts(lts: &Lts, aliases: &Aliases, repr: Repr) -> MimeBundle {
    let truncated = if lts.is_truncated() {
        " (truncated — state bound hit)"
    } else {
        ""
    };
    let mut plain = format!(
        "LTS: {} states, {} transitions{}\n",
        lts.num_states(),
        lts.num_transitions(),
        truncated,
    );
    for i in 0..lts.num_states() {
        plain.push_str(&format!(
            "  s{i}  {}\n",
            to_source_folded(lts.state(i), aliases)
        ));
    }
    for from in 0..lts.num_states() {
        for t in lts.transitions(from) {
            plain.push_str(&format!(
                "  s{from} --{}--> s{}\n",
                fold_name_ascii(&t.label, aliases),
                t.target,
            ));
        }
    }

    let text_latex = match repr {
        Repr::Ascii => None,
        Repr::Latex => {
            let state_rows: Vec<String> = (0..lts.num_states())
                .map(|i| format!(r"s_{{{i}}} & {}", to_latex_folded(lts.state(i), aliases)))
                .collect();
            let states = format!(
                r"\begin{{array}}{{rl}}{}\end{{array}}",
                state_rows.join(r" \\ ")
            );
            let mut edges: Vec<String> = Vec::new();
            for from in 0..lts.num_states() {
                for t in lts.transitions(from) {
                    edges.push(format!(
                        r"s_{{{from}}} \xrightarrow{{{}}} s_{{{}}}",
                        name_to_latex(&t.label, Some(aliases)),
                        t.target,
                    ));
                }
            }
            // Stack the state table over the transitions in one single-column array.
            let body = if edges.is_empty() {
                states
            } else {
                format!(
                    r"\begin{{array}}{{l}}{states} \\ {}\end{{array}}",
                    edges.join(r" \quad ")
                )
            };
            Some(display_math(&body))
        }
    };

    MimeBundle {
        text_plain: plain,
        text_latex,
    }
}

/// Render an equivalence [`Verdict`].
#[must_use]
pub fn render_verdict(v: &Verdict, repr: Repr) -> MimeBundle {
    let plain = match v {
        Verdict::Equivalent => "Equivalent".to_string(),
        Verdict::Distinguished(reason) => format!("Distinguished: {reason}"),
        Verdict::Inconclusive(reason) => format!("Inconclusive: {reason}"),
    };
    let text_latex = match repr {
        Repr::Ascii => None,
        Repr::Latex => match v {
            Verdict::Equivalent => Some(display_math(r"P \sim Q")),
            Verdict::Distinguished(reason) => Some(display_math(&format!(
                r"P \not\sim Q \quad (\text{{{}}})",
                escape_latex_text(reason)
            ))),
            Verdict::Inconclusive(_) => latex_status(&plain),
        },
    };
    MimeBundle {
        text_plain: plain,
        text_latex,
    }
}

/// Render a model-checking [`Checked`] result (holds + whether the LTS was fully
/// explored).
#[must_use]
pub fn render_checked(c: Checked, repr: Repr) -> MimeBundle {
    let verdict = if c.holds { "Holds" } else { "Does not hold" };
    let exactness = if c.exact {
        "exact"
    } else {
        "under-approximate (LTS truncated)"
    };
    let plain = format!("{verdict} ({exactness})");
    let text_latex = match repr {
        Repr::Ascii => None,
        Repr::Latex => {
            let sym = if c.holds { r"\models" } else { r"\not\models" };
            Some(display_math(&format!(
                r"{sym} \quad (\text{{{}}})",
                escape_latex_text(exactness)
            )))
        }
    };
    MimeBundle {
        text_plain: plain,
        text_latex,
    }
}

/// Render a typecheck outcome: `Ok` or the first [`TypeError`].
#[must_use]
pub fn render_typecheck(result: &Result<(), TypeError>, repr: Repr) -> MimeBundle {
    let plain = match result {
        Ok(()) => "well-typed".to_string(),
        Err(e) => format!("type error: {e}"),
    };
    let text_latex = match repr {
        Repr::Ascii => None,
        Repr::Latex => latex_status(&plain),
    };
    MimeBundle {
        text_plain: plain,
        text_latex,
    }
}

/// Render a run — a sequence of `(firing channel, state index)` steps produced
/// by a witness / counterexample / trace — as an ASCII listing over the LTS,
/// plus a LaTeX step array in LaTeX mode.
#[must_use]
pub fn render_run(
    title: &str,
    run: &[(Name, usize)],
    lts: &Lts,
    aliases: &Aliases,
    repr: Repr,
) -> MimeBundle {
    let mut plain = format!("{title}: {} step(s)\n", run.len());
    plain.push_str(&format!(
        "  s{}  {}\n",
        lts.initial(),
        to_source_folded(lts.state(lts.initial()), aliases),
    ));
    for (chan, state) in run {
        plain.push_str(&format!(
            "  --{}--> s{}  {}\n",
            fold_name_ascii(chan, aliases),
            state,
            to_source_folded(lts.state(*state), aliases),
        ));
    }

    let text_latex = match repr {
        Repr::Ascii => None,
        Repr::Latex => {
            let mut rows = vec![format!(
                r"& s_{{{}}} & {}",
                lts.initial(),
                to_latex_folded(lts.state(lts.initial()), aliases),
            )];
            for (chan, state) in run {
                rows.push(format!(
                    r"\xrightarrow{{{}}} & s_{{{state}}} & {}",
                    name_to_latex(chan, Some(aliases)),
                    to_latex_folded(lts.state(*state), aliases),
                ));
            }
            Some(display_math(&format!(
                r"\begin{{array}}{{rll}}{}\end{{array}}",
                rows.join(r" \\ ")
            )))
        }
    };

    MimeBundle {
        text_plain: plain,
        text_latex,
    }
}
