//! Rendering: turning toolkit values into rich [`MimeBundle`]s.
//!
//! Every renderer is *substrate-agnostic* — it produces a [`MimeBundle`] of
//! `text/plain` (always), plus optional `text/html` and `image/svg+xml`. The
//! Jupyter kernel (or any other front-end) maps those MIME keys onto its own
//! display messages; nothing here knows about ZeroMQ or Jupyter.
//!
//! The one external dependency is `layout-rs`, a pure-Rust DOT parser + layout
//! engine used to turn an [`Lts`]'s Graphviz `to_dot()` output into an inline
//! SVG — no system Graphviz binary is required. If layout fails (or panics on
//! some DOT it cannot handle) we fall back to the raw DOT in a `<pre>` block and
//! never propagate the failure.

use stratum::core::{canonicalize, Name, Proc};
use stratum::equiv::Verdict;
use stratum::logic::Checked;
use stratum::lts::{format_name, format_proc, Lts};
use stratum::syntax::{to_source, to_source_folded, Aliases};
use stratum::types::TypeError;

/// A rendered cell result as a set of alternative MIME representations.
///
/// `text_plain` is always present (the lowest-common-denominator fallback every
/// front-end can show). `text_html` and `image_svg` are richer alternatives a
/// capable front-end may prefer.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MimeBundle {
    /// `text/plain` representation. Always populated.
    pub text_plain: String,
    /// Optional `text/html` representation.
    pub text_html: Option<String>,
    /// Optional `image/svg+xml` representation.
    pub image_svg: Option<String>,
}

impl MimeBundle {
    /// A bundle carrying only `text/plain`.
    #[must_use]
    pub fn plain(text: impl Into<String>) -> Self {
        Self {
            text_plain: text.into(),
            text_html: None,
            image_svg: None,
        }
    }
}

/// Escape the five XML/HTML metacharacters so arbitrary process source can be
/// embedded in `text/html` safely.
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

/// Render a process as the *transparency pair*: the folded surface form (named
/// channels) alongside the expanded pure core (raw quoted-process names).
///
/// `text/plain` is the folded surface form; `text/html` shows both views so the
/// reader can see exactly what the sugar desugars to.
#[must_use]
pub fn render_proc(p: &Proc, aliases: &Aliases) -> MimeBundle {
    let folded = to_source_folded(p, aliases);
    let core = to_source(&canonicalize(p));
    let html = format!(
        "<div class=\"stratum-proc\">\
           <div><span style=\"color:#888\">surface&nbsp;</span><code>{}</code></div>\
           <div><span style=\"color:#888\">core&nbsp;&nbsp;&nbsp;&nbsp;</span><code>{}</code></div>\
         </div>",
        escape_html(&folded),
        escape_html(&core),
    );
    MimeBundle {
        text_plain: folded,
        text_html: Some(html),
        image_svg: None,
    }
}

/// Render an LTS: a state/transition summary in `text/plain`, and the graph as
/// an inline SVG (via `layout-rs`) when it can be laid out, else the raw DOT in
/// a `<pre>` fallback.
#[must_use]
pub fn render_lts(lts: &Lts) -> MimeBundle {
    let truncated = if lts.is_truncated() {
        " (truncated — state bound hit)"
    } else {
        ""
    };
    let summary = format!(
        "LTS: {} states, {} transitions{}",
        lts.num_states(),
        lts.num_transitions(),
        truncated,
    );
    let dot = lts.to_dot();
    match dot_to_svg(&dot) {
        Some(svg) => MimeBundle {
            text_plain: summary,
            text_html: None,
            image_svg: Some(svg),
        },
        None => MimeBundle {
            text_plain: summary,
            text_html: Some(format!(
                "<pre class=\"stratum-dot\">{}</pre>",
                escape_html(&dot)
            )),
            image_svg: None,
        },
    }
}

/// Render an equivalence [`Verdict`] as styled HTML.
#[must_use]
pub fn render_verdict(v: &Verdict) -> MimeBundle {
    let (plain, color, detail) = match v {
        Verdict::Equivalent => ("Equivalent".to_string(), "#2e7d32", String::new()),
        Verdict::Distinguished(reason) => (
            format!("Distinguished: {reason}"),
            "#c62828",
            format!(" — {}", escape_html(reason)),
        ),
        Verdict::Inconclusive(reason) => (
            format!("Inconclusive: {reason}"),
            "#f9a825",
            format!(" — {}", escape_html(reason)),
        ),
    };
    let label = match v {
        Verdict::Equivalent => "Equivalent",
        Verdict::Distinguished(_) => "Distinguished",
        Verdict::Inconclusive(_) => "Inconclusive",
    };
    let html = format!(
        "<div class=\"stratum-verdict\" style=\"color:{color}\"><b>{label}</b>{detail}</div>"
    );
    MimeBundle {
        text_plain: plain,
        text_html: Some(html),
        image_svg: None,
    }
}

/// Render a model-checking [`Checked`] result (holds + whether the LTS was fully
/// explored) as styled HTML.
#[must_use]
pub fn render_checked(c: Checked) -> MimeBundle {
    let (verdict, color) = if c.holds {
        ("Holds", "#2e7d32")
    } else {
        ("Does not hold", "#c62828")
    };
    let exactness = if c.exact {
        "exact"
    } else {
        "under-approximate (LTS truncated)"
    };
    let plain = format!("{verdict} ({exactness})");
    let html = format!(
        "<div class=\"stratum-checked\" style=\"color:{color}\"><b>{verdict}</b> \
         <span style=\"color:#888\">({exactness})</span></div>"
    );
    MimeBundle {
        text_plain: plain,
        text_html: Some(html),
        image_svg: None,
    }
}

/// Render a typecheck outcome as HTML: `Ok` or the first [`TypeError`].
#[must_use]
pub fn render_typecheck(result: &Result<(), TypeError>) -> MimeBundle {
    match result {
        Ok(()) => MimeBundle {
            text_plain: "well-typed".to_string(),
            text_html: Some("<div style=\"color:#2e7d32\"><b>well-typed</b></div>".to_string()),
            image_svg: None,
        },
        Err(e) => {
            let msg = e.to_string();
            MimeBundle {
                text_plain: format!("type error: {msg}"),
                text_html: Some(format!(
                    "<div style=\"color:#c62828\"><b>type error</b> — {}</div>",
                    escape_html(&msg)
                )),
                image_svg: None,
            }
        }
    }
}

/// Render a run — a sequence of `(firing channel, state index)` steps produced
/// by a witness / counterexample / trace — as an HTML table over the LTS, with a
/// `text/plain` fallback.
#[must_use]
pub fn render_run(title: &str, run: &[(Name, usize)], lts: &Lts) -> MimeBundle {
    // text/plain
    let mut plain = format!("{title}: {} step(s)\n", run.len());
    plain.push_str(&format!("  s{}\n", lts.initial()));
    for (chan, state) in run {
        plain.push_str(&format!(
            "  --{}--> s{}  {}\n",
            format_name(chan),
            state,
            format_proc(lts.state(*state)),
        ));
    }

    // text/html
    let mut rows = String::new();
    rows.push_str(&format!(
        "<tr><td>0</td><td><i>start</i></td><td>s{}</td><td><code>{}</code></td></tr>",
        lts.initial(),
        escape_html(&format_proc(lts.state(lts.initial()))),
    ));
    for (i, (chan, state)) in run.iter().enumerate() {
        rows.push_str(&format!(
            "<tr><td>{}</td><td><code>{}</code></td><td>s{}</td><td><code>{}</code></td></tr>",
            i + 1,
            escape_html(&format_name(chan)),
            state,
            escape_html(&format_proc(lts.state(*state))),
        ));
    }
    let html = format!(
        "<div class=\"stratum-run\"><b>{}</b> — {} step(s)\
         <table border=\"1\" cellpadding=\"4\" style=\"border-collapse:collapse\">\
         <tr><th>#</th><th>channel</th><th>state</th><th>process</th></tr>{}</table></div>",
        escape_html(title),
        run.len(),
        rows,
    );
    MimeBundle {
        text_plain: plain,
        text_html: Some(html),
        image_svg: None,
    }
}

/// Turn a Graphviz DOT string into an SVG string using the pure-Rust
/// `layout-rs` engine. Returns `None` if the DOT cannot be parsed or laid out
/// (including if `layout-rs` panics on it) — callers fall back to raw DOT.
#[must_use]
pub fn dot_to_svg(dot: &str) -> Option<String> {
    use layout::backends::svg::SVGWriter;
    use layout::gv::{DotParser, GraphBuilder};

    // `layout-rs` can panic on some DOT it does not fully support; contain it so
    // a rendering hiccup never brings down cell evaluation.
    let dot = dot.to_string();
    let result = std::panic::catch_unwind(move || {
        let mut parser = DotParser::new(&dot);
        let graph = parser.process().ok()?;
        let mut builder = GraphBuilder::new();
        builder.visit_graph(&graph);
        let mut vg = builder.get();
        let mut svg = SVGWriter::new();
        vg.do_it(false, false, false, &mut svg);
        Some(svg.finalize())
    });
    result.ok().flatten()
}
