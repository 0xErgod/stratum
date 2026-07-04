//! The DSL **completion + inspection** service: the substrate-agnostic half of a
//! notebook front-end's interactivity.
//!
//! Three pure functions, each panic-free on arbitrary input, back a front-end's
//! `complete` / `inspect` / `is_complete` requests (for Jupyter:
//! `complete_request` / `inspect_request` / `is_complete_request`). None of them
//! mutate the session; they read the [`Namespace`] and classify the code around
//! the cursor.
//!
//! ## Cursor units
//!
//! Jupyter's `cursor_pos` (protocol v5.3) is measured in **Unicode codepoints**
//! (`char`s), not bytes. Every offset this module consumes or produces
//! ([`Completions::cursor_start`] / [`Completions::cursor_end`]) is therefore a
//! codepoint offset. We work over a `Vec<char>` throughout and never index the
//! source by byte, so a multi-byte character before the cursor cannot corrupt
//! the reported range.

use stratum::core::{canonicalize, Proc};
use stratum::equiv::Verdict;
use stratum::logic::Checked;

use crate::eval::guard_nesting;
use crate::render::escape_html;
use crate::{Namespace, Obj};

/// The result of a completion request: the candidate strings and the codepoint
/// range they replace.
///
/// `cursor_start..cursor_end` is the span of the token under the cursor, in
/// **codepoint** offsets; a front-end substitutes a chosen `match` for exactly
/// that range.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Completions {
    /// The candidate completions, prefix-filtered, de-duplicated, stable order.
    pub matches: Vec<String>,
    /// Codepoint offset of the start of the replaced token.
    pub cursor_start: usize,
    /// Codepoint offset of the end of the replaced token (the cursor).
    pub cursor_end: usize,
}

/// The result of an inspection request: a plain-text summary plus an optional
/// richer HTML rendering.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Inspection {
    /// `text/plain` summary. Always populated when an [`Inspection`] is returned.
    pub text_plain: String,
    /// Optional `text/html` summary.
    pub text_html: Option<String>,
}

/// Whether a cell is ready to execute, needs more input, or is malformed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IsComplete {
    /// The cell parses; it can be executed.
    Complete,
    /// The cell is a well-formed *prefix* (unexpected EOF / unclosed bracket);
    /// the front-end should keep editing, indenting the next line by `indent`.
    Incomplete {
        /// Suggested indent for the continuation line.
        indent: String,
    },
    /// The cell has a hard syntax error; executing it would only error.
    Invalid,
}

/// The notebook directive names, without their leading `%`.
const DIRECTIVES: &[&str] = &[
    "explore",
    "expand",
    "check",
    "witness",
    "counterexample",
    "bisim",
    "step",
    "trace",
    "typecheck",
    "help",
];

/// The DSL surface keywords (as recognised by the `stratum-syntax` lexer).
const KEYWORDS: &[&str] = &["def", "new", "nil"];

/// The formula sub-language vocabulary offered inside `%check` / `%witness` /
/// `%counterexample`.
const FORMULA_VOCAB: &[&str] = &["EF", "EG", "AF", "AG", "EX", "emits("];

/// Directive keyword-argument tokens offered after a directive name.
const DIRECTIVE_ARGS: &[&str] = &["bound=", "por", "sym=", "weak", "obs=", "on", "->"];

/// Whether `c` may appear inside a DSL / directive identifier token.
fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

// ---------------------------------------------------------------------------
// complete
// ---------------------------------------------------------------------------

/// Context-aware completion for the token under the cursor.
///
/// `cursor_pos` and the returned [`Completions::cursor_start`] /
/// [`Completions::cursor_end`] are **codepoint** offsets (see the [module
/// docs](self)).
///
/// The candidate set depends on where the cursor sits:
///
/// * **Directive line** (`%…`): the directive *name* while still typing it, then
///   keyword args (`bound=`, `por`, …) and bound namespace names.
/// * **Formula** (inside `%check` / `%witness` / `%counterexample`): the temporal
///   vocabulary (`EF EG AF AG EX`, `emits(`) — and, inside `emits(…)`, the
///   resolvable channel names in scope.
/// * **DSL cell**: the keywords (`def`/`new`/`nil`), the stdlib macro names, the
///   `def`/`new`-bound names in the current cell, and bound namespace names.
#[must_use]
pub fn complete(code: &str, cursor_pos: usize, ns: &Namespace) -> Completions {
    let chars: Vec<char> = code.chars().collect();
    let cursor = cursor_pos.min(chars.len());

    // The token under the cursor: the run of word-chars ending at the cursor.
    let tok_start = {
        let mut i = cursor;
        while i > 0 && is_word(chars[i - 1]) {
            i -= 1;
        }
        i
    };
    let prefix: String = chars[tok_start..cursor].iter().collect();

    // The current line up to the cursor drives context detection.
    let line_start = chars[..cursor]
        .iter()
        .rposition(|&c| c == '\n')
        .map_or(0, |i| i + 1);
    let line_before: String = chars[line_start..cursor].iter().collect();
    let line_trim = line_before.trim_start();

    // Directive line: `%…` (but not a `%%`-magic, which we do not complete).
    if let Some(after) = line_trim.strip_prefix('%') {
        if !after.starts_with('%') {
            // Still typing the directive name itself (no whitespace yet)?
            if !line_trim[1..].contains(char::is_whitespace) {
                let matches = filtered(
                    DIRECTIVES.iter().map(|d| format!("%{d}")),
                    line_trim, // includes the leading `%`
                );
                // The replaced token starts at the `%`.
                let pct_start =
                    line_start + (line_before.chars().count() - line_trim.chars().count());
                return Completions {
                    matches,
                    cursor_start: pct_start,
                    cursor_end: cursor,
                };
            }
            // In the directive arguments.
            let dir = after.split_whitespace().next().unwrap_or("");
            let cands = directive_arg_candidates(dir, &line_before, ns);
            return Completions {
                matches: filtered(cands.into_iter(), &prefix),
                cursor_start: tok_start,
                cursor_end: cursor,
            };
        }
    }

    // Otherwise a DSL cell.
    let cands = dsl_candidates(code, ns);
    Completions {
        matches: filtered(cands.into_iter(), &prefix),
        cursor_start: tok_start,
        cursor_end: cursor,
    }
}

/// Candidate tokens for a position inside a directive's arguments.
fn directive_arg_candidates(dir: &str, line_before: &str, ns: &Namespace) -> Vec<String> {
    match dir {
        "check" | "witness" | "counterexample" => {
            if inside_emits(line_before) {
                // Only channel names resolve inside `emits(...)`.
                let mut out = ns.channel_names();
                out.extend(scan_cell_names(line_before));
                out
            } else {
                let mut out: Vec<String> = FORMULA_VOCAB.iter().map(|s| (*s).to_string()).collect();
                out.push("on".to_string());
                out.extend(ns.binding_names());
                out
            }
        }
        _ => {
            let mut out: Vec<String> = DIRECTIVE_ARGS.iter().map(|s| (*s).to_string()).collect();
            out.extend(ns.binding_names());
            out
        }
    }
}

/// Candidate tokens for a DSL cell: keywords, stdlib macros, cell-local
/// `def`/`new` names, and bound namespace names.
fn dsl_candidates(code: &str, ns: &Namespace) -> Vec<String> {
    let mut out: Vec<String> = KEYWORDS.iter().map(|s| (*s).to_string()).collect();
    out.extend(stdlib_macro_names());
    out.extend(scan_cell_names(code));
    out.extend(ns.binding_names());
    out
}

/// Whether the cursor sits inside an unclosed `emits(` in `line_before`.
fn inside_emits(line_before: &str) -> bool {
    match line_before.rfind("emits(") {
        Some(l) => line_before.rfind(')').is_none_or(|r| r < l),
        None => false,
    }
}

/// Prefix-filter an iterator of candidates, de-duplicating while preserving the
/// first occurrence (a stable order).
fn filtered(cands: impl Iterator<Item = String>, prefix: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for c in cands {
        if c.starts_with(prefix) && !out.contains(&c) {
            out.push(c);
        }
    }
    out
}

/// The stdlib macro names, harvested from [`stratum::encodings::STDLIB`] so the
/// list stays in sync with the shipped encodings (`bang`, `contract`, …).
fn stdlib_macro_names() -> Vec<String> {
    let mut out = Vec::new();
    for line in stratum::encodings::STDLIB.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("def ") {
            let name: String = rest
                .trim_start()
                .chars()
                .take_while(|c| is_word(*c))
                .collect();
            if !name.is_empty() && !out.contains(&name) {
                out.push(name);
            }
        }
    }
    out
}

/// Harvest the identifiers introduced by `new …` / `def …` declarations in a
/// cell, so partially-typed cells still offer their own names.
///
/// A lightweight line scan — deliberately not a full parse, so it works on the
/// incomplete cells that completion is most useful for. `new a, b` contributes
/// `a` and `b`; `def foo(...)` and `def foo { ... }` contribute `foo`.
fn scan_cell_names(code: &str) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for raw_line in code.lines() {
        let line = raw_line.trim_start();
        if let Some(rest) = line.strip_prefix("new ") {
            for tok in rest.split([',', ' ', '\t']) {
                let name: String = tok.chars().take_while(|c| is_word(*c)).collect();
                if !name.is_empty() && !out.contains(&name) {
                    out.push(name);
                }
            }
        } else if let Some(rest) = line.strip_prefix("def ") {
            let name: String = rest
                .trim_start()
                .chars()
                .take_while(|c| is_word(*c))
                .collect();
            if !name.is_empty() && !out.contains(&name) {
                out.push(name);
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// inspect
// ---------------------------------------------------------------------------

/// Documentation for the token under the cursor, or `None` if nothing about it
/// is worth surfacing.
///
/// Resolution order for the token: a bound **namespace name** (summarise its
/// [`Obj`]), a **directive** (`%name` or a directive word on a `%`-line), a
/// **stdlib macro** (its definition), a **keyword**, or a **formula modality**.
///
/// `cursor_pos` is a **codepoint** offset (see the [module docs](self)).
#[must_use]
pub fn inspect(code: &str, cursor_pos: usize, ns: &Namespace) -> Option<Inspection> {
    let chars: Vec<char> = code.chars().collect();
    let cursor = cursor_pos.min(chars.len());

    // The full token spanning the cursor (extend both directions).
    let mut start = cursor;
    while start > 0 && is_word(chars[start - 1]) {
        start -= 1;
    }
    let mut end = cursor;
    while end < chars.len() && is_word(chars[end]) {
        end += 1;
    }
    let token: String = chars[start..end].iter().collect();
    if token.is_empty() {
        return None;
    }

    // Is the token the name of a `%`-directive (either `%token` or a bare
    // directive word on a line that starts with `%`)?
    let preceded_by_pct = start > 0 && chars[start - 1] == '%';
    let line_start = chars[..start]
        .iter()
        .rposition(|&c| c == '\n')
        .map_or(0, |i| i + 1);
    let on_directive_line = chars[line_start..end]
        .iter()
        .collect::<String>()
        .trim_start()
        .starts_with('%');

    // 1. A bound namespace object always wins.
    if let Some(obj) = ns.get(&token) {
        return Some(inspect_obj(&token, obj, ns));
    }

    // 2. A directive.
    if (preceded_by_pct || on_directive_line) && DIRECTIVES.contains(&token.as_str()) {
        return Some(directive_doc(&token));
    }

    // 3. A stdlib macro.
    if stdlib_macro_names().contains(&token) {
        return macro_doc(&token);
    }

    // 4. A keyword.
    if KEYWORDS.contains(&token.as_str()) {
        return Some(keyword_doc(&token));
    }

    // 5. A formula modality.
    if let Some(doc) = formula_doc(&token) {
        return Some(doc);
    }

    None
}

/// Summarise a bound [`Obj`] for inspection.
fn inspect_obj(name: &str, obj: &Obj, ns: &Namespace) -> Inspection {
    let text = match obj {
        Obj::Proc(p) => {
            let folded = stratum::syntax::to_source_folded(p, ns.aliases());
            let core = stratum::syntax::to_source(&canonicalize(p));
            format!(
                "proc `{name}`\n  surface:      {folded}\n  core:         {core}\n  \
                 free variables: {}\n  quote depth:  {}",
                p.free_vars().len(),
                Proc::quote_depth(p),
            )
        }
        Obj::Lts { lts, reduction } => {
            let truncated = if lts.is_truncated() {
                "yes (state bound hit)"
            } else {
                "no"
            };
            format!(
                "lts `{name}`\n  states:      {}\n  transitions: {}\n  truncated:   {}\n  \
                 reduction:   {}",
                lts.num_states(),
                lts.num_transitions(),
                truncated,
                reduction.label(),
            )
        }
        Obj::Verdict(v) => {
            let value = match v {
                Verdict::Equivalent => "Equivalent".to_string(),
                Verdict::Distinguished(r) => format!("Distinguished — {r}"),
                Verdict::Inconclusive(r) => format!("Inconclusive — {r}"),
            };
            format!("verdict `{name}`\n  {value}")
        }
        Obj::Checked(Checked { holds, exact }) => {
            let verdict = if *holds { "holds" } else { "does not hold" };
            let exactness = if *exact {
                "exact"
            } else {
                "under-approximate (LTS truncated)"
            };
            format!("checked `{name}`\n  {verdict} ({exactness})")
        }
        Obj::Bool(b) => format!("bool `{name}`\n  {b}"),
        Obj::Text(t) => format!("text `{name}`\n  {t}"),
    };
    Inspection {
        text_html: Some(format!(
            "<pre class=\"stratum-inspect\">{}</pre>",
            escape_html(&text)
        )),
        text_plain: text,
    }
}

/// A concise doc for a `%`-directive.
fn directive_doc(name: &str) -> Inspection {
    let body = match name {
        "explore" => {
            "%explore <p> [bound=N] [por] [obs=a,b] [sym=a,b] -> lts\n\
             Build the bounded trace LTS of a process (or inline DSL). `por` / `sym=` \
             apply partial-order / symmetry reduction; `-> name` binds the result."
        }
        "expand" => {
            "%expand <p>\n\
             Show the desugared pure core of a process (all `def`/`new`/macro sugar removed)."
        }
        "check" => {
            "%check <formula> on <lts>\n\
             Model-check a temporal formula against a bound LTS (holds + exactness)."
        }
        "witness" => {
            "%witness <formula> on <lts>\n\
             Exhibit a run of the LTS that reaches the formula's goal."
        }
        "counterexample" => {
            "%counterexample <invariant> on <lts>\n\
             Exhibit a run of the LTS that violates the invariant."
        }
        "bisim" => {
            "%bisim <p> <q> [weak] [obs=a,b]\n\
             Decide barbed (bi)simulation of two processes over an observation set."
        }
        "step" => {
            "%step <p>\n\
             List the one-step reducts of a process."
        }
        "trace" => {
            "%trace <lts>\n\
             Follow a sample run from the LTS's initial state."
        }
        "typecheck" => {
            "%typecheck <p> [with a:Ty, b:Ty]\n\
             Channel-sort typecheck a process under an optional environment."
        }
        "help" => {
            "%help\n\
             List the notebook directive vocabulary."
        }
        _ => "unknown directive",
    };
    let text = format!("directive `%{name}`\n{body}");
    plain_html(text)
}

/// A doc for a stdlib macro, showing its `def` definition.
fn macro_doc(name: &str) -> Option<Inspection> {
    let def = stratum::encodings::STDLIB
        .lines()
        .map(str::trim)
        .find(|l| {
            l.strip_prefix("def ")
                .is_some_and(|r| r.trim_start().starts_with(name))
        })?;
    let role = match name {
        "bang" => "replication `!P` (§3) — spawns unboundedly many copies of P.",
        "contract" => "input-guarded replication `!C(y).P` (§3) — a persistent server on C.",
        _ => "a derived ρ-calculus operator (stdlib encoding).",
    };
    let text = format!("macro `{name}`\n  {role}\n  {def}");
    Some(plain_html(text))
}

/// A doc for a DSL keyword.
fn keyword_doc(name: &str) -> Inspection {
    let body = match name {
        "def" => {
            "def NAME { BODY }  or  def NAME(p1, …) { BODY }\n\
             Bind a name/process alias, or define a parameterized macro (an encoding). \
             Pure surface sugar: expanded away at parse time."
        }
        "new" => {
            "new n1, …, nk\n\
             Mint k distinct fresh ground channel names (name generation, not ν-restriction)."
        }
        "nil" => {
            "nil  (also `0`)\n\
             The null process."
        }
        _ => "unknown keyword",
    };
    let text = format!("keyword `{name}`\n{body}");
    plain_html(text)
}

/// A doc for a formula modality / atom, or `None` for a non-formula word.
fn formula_doc(name: &str) -> Option<Inspection> {
    let body = match name {
        "EF" => "EF φ — φ holds on some reachable state (possibly-eventually).",
        "AF" => "AF φ — φ holds on every maximal run eventually (inevitably).",
        "EG" => "EG φ — some run keeps φ true forever.",
        "AG" => "AG φ — φ holds on every reachable state (invariant).",
        "EX" => {
            "EX φ — φ holds in some immediate successor (next-time; not preserved under reduction)."
        }
        "emits" => {
            "emits(<name>) — the atomic proposition: a top-level OUTPUT barb on the named channel."
        }
        _ => return None,
    };
    Some(plain_html(format!("formula `{name}`\n{body}")))
}

/// Wrap a plain-text doc in an [`Inspection`] with an escaped `<pre>` HTML view.
fn plain_html(text: String) -> Inspection {
    Inspection {
        text_html: Some(format!(
            "<pre class=\"stratum-inspect\">{}</pre>",
            escape_html(&text)
        )),
        text_plain: text,
    }
}

// ---------------------------------------------------------------------------
// is_complete
// ---------------------------------------------------------------------------

/// Classify whether a cell is ready to execute.
///
/// Uses the toolkit parser: a cell that parses is [`IsComplete::Complete`]; a
/// well-formed prefix that hits an unexpected end-of-input / unclosed bracket is
/// [`IsComplete::Incomplete`] (with a small suggested indent); any other syntax
/// error is [`IsComplete::Invalid`]. Directives / magics are treated as
/// single-shot [`IsComplete::Complete`] lines. The [`guard_nesting`] guard is
/// reused so a pathologically nested cell cannot overflow the parser stack.
#[must_use]
pub fn is_complete(code: &str) -> IsComplete {
    let trimmed = code.trim();
    // Empty or directive/magic cells are executed as-is.
    if trimmed.is_empty() || trimmed.starts_with('%') {
        return IsComplete::Complete;
    }

    // A DSL cell: strip an optional leading `name =` binding, exactly as the
    // evaluator does, then try to parse the process.
    let (_binding, source) = crate::eval::split_binding(code);
    if guard_nesting(source).is_err() {
        // Too deeply nested to hand to the parser — a hard reject, not a prefix.
        return IsComplete::Invalid;
    }

    match stratum::syntax::parse_with_aliases(source) {
        Ok(_) => IsComplete::Complete,
        Err(e) => {
            // The parser reports `found end of input` for a well-formed prefix
            // (unclosed bracket, dangling `.`, unfinished output). Anything else
            // is a genuine syntax error.
            if e.message.contains("end of input") {
                IsComplete::Incomplete {
                    indent: "    ".to_string(),
                }
            } else {
                IsComplete::Invalid
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::evaluate;

    /// A session namespace with a bound proc `srv` (minting channel `a`) and a
    /// bound LTS `g`.
    fn seeded() -> Namespace {
        let mut ns = Namespace::new();
        let _ = evaluate("srv = new a\na!(0)", &mut ns);
        let _ = evaluate("%explore srv -> g", &mut ns);
        ns
    }

    // ---- complete: directive context -------------------------------------

    #[test]
    fn complete_directive_names() {
        let ns = Namespace::new();
        let c = complete("%exp", 4, &ns);
        assert!(c.matches.contains(&"%explore".to_string()));
        assert!(c.matches.contains(&"%expand".to_string()));
        // The replaced token spans the `%`.
        assert_eq!(c.cursor_start, 0);
        assert_eq!(c.cursor_end, 4);
    }

    #[test]
    fn complete_directive_args_include_namespace_names() {
        let ns = seeded();
        // After the directive name, keyword args + bound namespace names.
        let c = complete("%explore ", 9, &ns);
        assert!(c.matches.iter().any(|m| m == "bound="));
        assert!(c.matches.contains(&"srv".to_string()));
        assert!(c.matches.contains(&"g".to_string()));
    }

    // ---- complete: formula / emits context -------------------------------

    #[test]
    fn complete_formula_vocab() {
        let ns = seeded();
        let c = complete("%check E", 8, &ns);
        assert!(c.matches.contains(&"EF".to_string()));
        assert!(c.matches.contains(&"EG".to_string()));
        assert!(c.matches.contains(&"EX".to_string()));
        assert!(!c.matches.iter().any(|m| m == "AF")); // filtered by prefix `E`
    }

    #[test]
    fn complete_inside_emits_offers_channels() {
        let ns = seeded();
        // Inside an unclosed `emits(`, only channel names are resolvable.
        let c = complete("%check emits(", 13, &ns);
        assert!(c.matches.contains(&"a".to_string()));
        assert!(!c.matches.iter().any(|m| m == "EF"));
    }

    // ---- complete: DSL context -------------------------------------------

    #[test]
    fn complete_dsl_keyword_macro_and_names() {
        let ns = seeded();
        assert!(complete("ne", 2, &ns).matches.contains(&"new".to_string()));
        assert!(complete("ba", 2, &ns).matches.contains(&"bang".to_string()));
        assert!(complete("con", 3, &ns)
            .matches
            .contains(&"contract".to_string()));
        // A bound namespace name.
        assert!(complete("sr", 2, &ns).matches.contains(&"srv".to_string()));
    }

    #[test]
    fn complete_cell_local_new_name() {
        let ns = Namespace::new();
        // `foo` is minted by this cell's own `new`, not yet in the namespace.
        let c = complete("new foo\nf", 9, &ns);
        assert!(c.matches.contains(&"foo".to_string()));
        assert_eq!(c.cursor_start, 8);
        assert_eq!(c.cursor_end, 9);
    }

    // ---- complete: codepoint cursor correctness --------------------------

    #[test]
    fn complete_codepoints_not_bytes() {
        let ns = Namespace::new();
        // `π` is one codepoint but two UTF-8 bytes. In codepoints the token
        // `ne` starts at offset 2; a byte-based impl would report 3.
        let code = "\u{03c0} ne";
        assert_eq!(code.chars().count(), 4);
        let c = complete(code, 4, &ns);
        assert_eq!(c.cursor_start, 2);
        assert_eq!(c.cursor_end, 4);
        assert!(c.matches.contains(&"new".to_string()));
    }

    #[test]
    fn complete_empty_and_boundary_cursors() {
        let ns = Namespace::new();
        // Empty input: a valid (empty) range, non-empty candidate list.
        let c = complete("", 0, &ns);
        assert_eq!((c.cursor_start, c.cursor_end), (0, 0));
        assert!(!c.matches.is_empty());
        // Cursor at the very start of a token: prefix is empty.
        let c = complete("new", 0, &ns);
        assert_eq!((c.cursor_start, c.cursor_end), (0, 0));
        // Cursor at the very end: prefix is the whole token.
        let c = complete("new", 3, &ns);
        assert_eq!((c.cursor_start, c.cursor_end), (0, 3));
        assert!(c.matches.contains(&"new".to_string()));
    }

    #[test]
    fn complete_out_of_range_cursor_is_clamped() {
        let ns = Namespace::new();
        // A cursor past the end must not panic; it clamps to the length.
        let c = complete("new", 999, &ns);
        assert_eq!(c.cursor_end, 3);
    }

    // ---- inspect ---------------------------------------------------------

    #[test]
    fn inspect_bound_proc() {
        let ns = seeded();
        let i = inspect("srv", 1, &ns).expect("srv is bound");
        assert!(i.text_plain.contains("proc `srv`"));
        assert!(i.text_plain.contains("surface"));
        assert!(i.text_plain.contains("core"));
        assert!(i.text_html.is_some());
    }

    #[test]
    fn inspect_bound_lts() {
        let ns = seeded();
        let i = inspect("g", 0, &ns).expect("g is bound");
        assert!(i.text_plain.contains("lts `g`"));
        assert!(i.text_plain.contains("states"));
        assert!(i.text_plain.contains("transitions"));
    }

    #[test]
    fn inspect_keyword() {
        let ns = Namespace::new();
        let i = inspect("new", 1, &ns).expect("keyword doc");
        assert!(i.text_plain.contains("keyword `new`"));
    }

    #[test]
    fn inspect_directive() {
        let ns = Namespace::new();
        let i = inspect("%explore", 3, &ns).expect("directive doc");
        assert!(i.text_plain.contains("directive `%explore`"));
    }

    #[test]
    fn inspect_stdlib_macro() {
        let ns = Namespace::new();
        let i = inspect("bang", 2, &ns).expect("macro doc");
        assert!(i.text_plain.contains("macro `bang`"));
        assert!(i.text_plain.contains("def bang"));
    }

    #[test]
    fn inspect_unknown_is_none() {
        let ns = Namespace::new();
        assert!(inspect("zzz_unbound", 2, &ns).is_none());
        // Cursor on whitespace: no token.
        assert!(inspect("a b", 1, &ns).is_none());
    }

    // ---- is_complete -----------------------------------------------------

    #[test]
    fn is_complete_full_proc() {
        assert_eq!(is_complete("new a\na!(0)"), IsComplete::Complete);
        assert_eq!(is_complete("@0!(0)"), IsComplete::Complete);
        assert_eq!(is_complete(""), IsComplete::Complete);
        assert_eq!(is_complete("%explore srv"), IsComplete::Complete);
    }

    #[test]
    fn is_complete_incomplete_prefixes() {
        assert!(matches!(
            is_complete("a(x)."),
            IsComplete::Incomplete { .. }
        ));
        assert!(matches!(is_complete("("), IsComplete::Incomplete { .. }));
        assert!(matches!(
            is_complete("@0(y).("),
            IsComplete::Incomplete { .. }
        ));
    }

    #[test]
    fn is_complete_invalid() {
        assert_eq!(is_complete(")"), IsComplete::Invalid);
        assert_eq!(is_complete("#$%^ garbage"), IsComplete::Invalid);
    }

    // ---- panic-safety ----------------------------------------------------

    #[test]
    fn panic_safe_on_deep_and_garbage_input() {
        let ns = seeded();
        let deep = "(".repeat(5000);
        // None of these may panic on pathological input.
        let _ = complete(&deep, deep.chars().count(), &ns);
        let _ = inspect(&deep, 10, &ns);
        assert_eq!(is_complete(&deep), IsComplete::Invalid);

        let garbage = "@#$%^&*()_+{}|:<>?~`";
        let _ = complete(garbage, 3, &ns);
        let _ = inspect(garbage, 3, &ns);
        let _ = is_complete(garbage);

        // A cursor in the middle of a multi-byte run, deep formula, etc.
        let uni = "caf\u{e9} \u{03c0} \u{03bb} emits(".repeat(50);
        let _ = complete(&uni, uni.chars().count() / 2, &ns);
        let _ = inspect(&uni, 5, &ns);
    }
}
