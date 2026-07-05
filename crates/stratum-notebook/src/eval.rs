//! The cell evaluator: DSL cells, `#define` bindings, `#`-directives, and the
//! `#rune` script cell.
//!
//! This is the substrate-agnostic heart of the notebook. [`evaluate`] classifies
//! a cell, runs it against the session [`Namespace`], and returns a
//! [`CellOutcome`] of rich displays / streamed stdout / a structured error. All
//! toolkit logic (parse, explore, check, bisim, typecheck) is invoked here and
//! immediately rendered; nothing panics on bad input.

use stratum::core::{canonicalize, name_equiv, step_labeled, Name, Proc};
use stratum::equiv::{strong_barbed_bisimilar, weak_barbed_bisimilar};
use stratum::logic::{counterexample, holds_checked, witness};
use stratum::lts::{format_name, traces, EventKey, Lts, Trace};
use stratum::syntax::{name_to_latex, parse_with_aliases, to_latex, to_source, ParseError};
use stratum::types::{check as typecheck, Env, Ty};

use crate::formula::parse_formula;
use crate::render::{
    display_math, render_checked, render_core, render_lts, render_proc, render_run, render_trace,
    render_traces, render_typecheck, render_verdict, MimeBundle,
};
use crate::{default_observations, CellError, CellOutcome, Namespace, Obj, Reduction, Repr};

/// The default bounded-exploration state cap for directives that build an LTS.
const DEFAULT_BOUND: usize = 1000;

/// Maximum bracket-nesting depth accepted in any string handed to the toolkit
/// parsers (`parse_with_aliases`, `expand`, the `Chan(..)` type parser). Those
/// parsers recurse without a depth guard (issue #43), so a pathologically nested
/// input would overflow the native stack and abort the whole process —
/// uncatchable by `catch_unwind`. We reject over-deep input up front with a
/// clean error. The scan is a conservative over-approximation (it counts every
/// bracket kind and ignores matching), which is fine: rejecting a pathological
/// cell is always preferable to crashing.
const MAX_NESTING_DEPTH: usize = 256;

/// Reject a string whose maximum bracket/paren/brace nesting exceeds
/// [`MAX_NESTING_DEPTH`], before it reaches a non-depth-guarded toolkit parser.
pub(crate) fn guard_nesting(src: &str) -> Result<(), CellError> {
    let mut depth: usize = 0;
    let mut max: usize = 0;
    for c in src.chars() {
        match c {
            '(' | '[' | '{' => {
                depth += 1;
                max = max.max(depth);
            }
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    if max > MAX_NESTING_DEPTH {
        Err(CellError::new(
            "NestingError",
            format!("input nesting too deep (max {MAX_NESTING_DEPTH})"),
        ))
    } else {
        Ok(())
    }
}

/// Evaluate one notebook cell against the session namespace.
#[must_use]
pub fn evaluate(cell: &str, ns: &mut Namespace) -> CellOutcome {
    let trimmed = cell.trim();
    if trimmed.is_empty() {
        return CellOutcome::default();
    }
    // `#rune` is a script cell that runs an embedded Rune program and produces its
    // own full outcome (captured stdout + a rendered return value + any error), so
    // it is dispatched before the generic display/err mapping below.
    if let Some(body) = strip_rune_magic(trimmed) {
        return crate::script::run_rune(body, ns);
    }
    // A leading `#` introduces a *meta* line: the first word selects the mode
    // (`define` to bind this cell's result, a directive name, or `help`).
    // Everything else is a bare DSL cell that binds to an auto-generated name.
    let result = if let Some(rest) = trimmed.strip_prefix('#') {
        run_meta(rest, ns)
    } else {
        run_dsl(cell, None, ns)
    };
    match result {
        Ok(displays) => CellOutcome {
            displays,
            stream_stdout: String::new(),
            error: None,
        },
        Err(e) => CellOutcome::err(e),
    }
}

// ---------------------------------------------------------------------------
// `#rune` script cells
// ---------------------------------------------------------------------------

/// If `cell` is a `#rune` script cell, return the script body (everything after
/// the `#rune` line); otherwise `None`. Any text on the same line as `#rune` is
/// treated as part of the meta line and dropped.
fn strip_rune_magic(cell: &str) -> Option<&str> {
    let rest = cell.strip_prefix('#')?;
    let (name, _) = split_first_word(rest);
    if name != "rune" {
        return None;
    }
    Some(match cell.find('\n') {
        Some(i) => &cell[i + 1..],
        None => "",
    })
}

// ---------------------------------------------------------------------------
// Meta lines: `#define`, directives, `#help`
// ---------------------------------------------------------------------------

/// Dispatch a `#`-meta cell. `rest` is the cell body with the leading `#`
/// already stripped; its first word selects the mode.
fn run_meta(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (kw, after) = split_first_word(rest);
    match kw {
        "define" => run_define(after, ns),
        "explore" => dir_explore(after.trim(), ns),
        "expand" => dir_expand(after.trim(), ns),
        "check" => dir_check(after.trim(), ns),
        "witness" => dir_witness(after.trim(), ns),
        "counterexample" => dir_counterexample(after.trim(), ns),
        "bisim" => dir_bisim(after.trim(), ns),
        "step" => dir_step(after.trim(), ns),
        "traces" => dir_traces(after.trim(), ns),
        "trace" => dir_trace(after.trim(), ns),
        "lin" => dir_lin(after.trim(), ns),
        "project" => dir_project(after.trim(), ns),
        "typecheck" => dir_typecheck(after.trim(), ns),
        "ascii" => dir_repr(Some(Repr::Ascii), ns),
        "latex" => dir_repr(Some(Repr::Latex), ns),
        "repr" => dir_repr(None, ns),
        "help" => Ok(vec![help_bundle()]),
        other => Err(CellError::new(
            "DirectiveError",
            format!("unknown directive `#{other}`. Try `#help`."),
        )),
    }
}

/// `#ascii` / `#latex` set the session output representation; `#repr` (a `None`
/// argument) just reports the current mode.
fn dir_repr(mode: Option<Repr>, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    if let Some(mode) = mode {
        ns.set_repr(mode);
    }
    Ok(vec![MimeBundle::plain(format!(
        "representation: {}",
        ns.repr().label()
    ))])
}

// ---------------------------------------------------------------------------
// DSL cells and `#define`
// ---------------------------------------------------------------------------

/// `#define <name> [<expr>]` — bind this cell's process to `name`. The value is
/// everything after the name, whether on the same line (`#define e @0!(0)`) or
/// on the lines below the header (`#define hs` then the Stratum code).
fn run_define(after: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (name, source) = split_first_word(after);
    if !is_ident(name) {
        return Err(CellError::new(
            "DefineError",
            "`#define` needs a name: `#define NAME` then Stratum code on the \
             following lines, or `#define NAME <expr>` inline"
                .to_string(),
        ));
    }
    let source = source.trim();
    if source.is_empty() {
        return Err(CellError::new(
            "DefineError",
            format!("`#define {name}` has no body — put the Stratum code below it, or inline after the name"),
        ));
    }
    run_dsl(source, Some(name.to_string()), ns)
}

/// Parse a DSL `source` into a process, bind it under `name` (or an
/// auto-generated name when `None`), and render it.
fn run_dsl(
    source: &str,
    name: Option<String>,
    ns: &mut Namespace,
) -> Result<Vec<MimeBundle>, CellError> {
    guard_nesting(source)?;
    let (proc, aliases) = parse_with_aliases(source).map_err(|e| parse_error(source, &e))?;
    ns.absorb_aliases(&proc, aliases);
    let bundle = render_proc(&proc, ns.aliases(), ns.repr());
    let name = name.unwrap_or_else(|| ns.next_auto_name());
    ns.insert(name, Obj::Proc(proc));
    Ok(vec![bundle])
}

/// `#explore <procname|inline DSL> [bound=N] [por] [obs=a,b] [sym=a,b] -> name`
fn dir_explore(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (pre, bind) = split_arrow(rest);
    let opts = Opts::parse(pre);
    let target = opts.target.trim();
    if target.is_empty() {
        return arity_err(
            "explore",
            "#explore <procname|DSL> [bound=N] [por] [sym=a,b] -> name",
        );
    }
    let proc = resolve_proc(target, ns)?;
    let bound = opts.bound.unwrap_or(DEFAULT_BOUND);

    let (lts, reduction) = if opts.por {
        let observed = resolve_names(&opts.obs, ns)?;
        (Lts::explore_por(&proc, bound, &observed), Reduction::Por)
    } else if !opts.sym.is_empty() {
        let interchangeable = resolve_names(&opts.sym, ns)?;
        (
            Lts::explore_symmetric(&proc, bound, &interchangeable),
            Reduction::Symmetry,
        )
    } else {
        (Lts::explore(&proc, bound), Reduction::None)
    };

    let bundle = apply_caveat(render_lts(&lts, ns.aliases(), ns.repr()), reduction);
    if let Some(name) = bind {
        ns.insert(name, Obj::Lts { lts, reduction });
    }
    Ok(vec![bundle])
}

/// `#expand <procname|inline DSL>` — show the desugared pure core.
fn dir_expand(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let target = rest.trim();
    if target.is_empty() {
        return arity_err("expand", "#expand <procname|DSL>");
    }
    let proc = resolve_proc(target, ns)?;
    Ok(vec![render_core(&proc, ns.repr())])
}

/// `#check <formula> on <ltsname>`
fn dir_check(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (formula_src, lts_name) = split_on(rest, " on ")
        .ok_or_else(|| CellError::new("DirectiveError", "usage: #check <formula> on <ltsname>"))?;
    let (lts, reduction) = lookup_lts_binding(lts_name.trim(), ns)?;
    let compiled = compile_formula(formula_src.trim(), ns)?;
    reject_ex_on_reduced(&compiled, reduction)?;
    let label = compiled.labelling();
    let checked = holds_checked(lts, &compiled.formula, &label);
    Ok(vec![apply_caveat(
        render_checked(checked, ns.repr()),
        reduction,
    )])
}

/// `#witness <formula> on <ltsname>`
fn dir_witness(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (formula_src, lts_name) = split_on(rest, " on ").ok_or_else(|| {
        CellError::new("DirectiveError", "usage: #witness <formula> on <ltsname>")
    })?;
    let (lts, reduction) = lookup_lts_binding(lts_name.trim(), ns)?;
    let compiled = compile_formula(formula_src.trim(), ns)?;
    reject_ex_on_reduced(&compiled, reduction)?;
    let label = compiled.labelling();
    let bundle = match witness(lts, &compiled.formula, &label) {
        Some(run) => render_run("witness", &run, lts, ns.aliases(), ns.repr()),
        None => MimeBundle::plain("no witness: the goal is unreachable in the explored LTS"),
    };
    Ok(vec![apply_caveat(bundle, reduction)])
}

/// `#counterexample <invariant> on <ltsname>`
fn dir_counterexample(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (formula_src, lts_name) = split_on(rest, " on ").ok_or_else(|| {
        CellError::new(
            "DirectiveError",
            "usage: #counterexample <invariant> on <ltsname>",
        )
    })?;
    let (lts, reduction) = lookup_lts_binding(lts_name.trim(), ns)?;
    let compiled = compile_formula(formula_src.trim(), ns)?;
    reject_ex_on_reduced(&compiled, reduction)?;
    let label = compiled.labelling();
    let bundle = match counterexample(lts, &compiled.formula, &label) {
        Some(run) => render_run("counterexample", &run, lts, ns.aliases(), ns.repr()),
        None => {
            MimeBundle::plain("no counterexample: the invariant holds throughout the explored LTS")
        }
    };
    Ok(vec![apply_caveat(bundle, reduction)])
}

/// `#bisim <p> <q> [weak] [obs=a,b] [bound=N]`
fn dir_bisim(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let opts = Opts::parse(rest);
    let mut words = opts.target.split_whitespace();
    let p_name = words.next();
    let q_name = words.next();
    let (Some(pn), Some(qn)) = (p_name, q_name) else {
        return arity_err("bisim", "#bisim <p> <q> [weak] [obs=a,b]");
    };
    if words.next().is_some() {
        return Err(CellError::new(
            "DirectiveError",
            "`#bisim` takes exactly two processes (extra arguments given). \
             Usage: #bisim <p> <q> [weak] [obs=a,b]",
        ));
    }
    let p = resolve_proc(pn, ns)?;
    let q = resolve_proc(qn, ns)?;
    let bound = opts.bound.unwrap_or(DEFAULT_BOUND);
    let obs = if opts.obs.is_empty() {
        default_observations(&p, &q)
    } else {
        resolve_names(&opts.obs, ns)?
    };
    let verdict = if opts.weak {
        weak_barbed_bisimilar(&p, &q, &obs, bound)
    } else {
        strong_barbed_bisimilar(&p, &q, &obs, bound)
    };
    Ok(vec![render_verdict(&verdict, ns.repr())])
}

/// `#step <procname|inline DSL>` — the one-step reducts.
fn dir_step(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let target = rest.trim();
    if target.is_empty() {
        return arity_err("step", "#step <procname|DSL>");
    }
    let proc = resolve_proc(target, ns)?;
    let steps = step_labeled(&proc);
    if steps.is_empty() {
        return Ok(vec![MimeBundle::plain("no reductions (terminal)")]);
    }
    let mut plain = format!("{} one-step reduct(s):\n", steps.len());
    for (i, s) in steps.iter().enumerate() {
        plain.push_str(&format!(
            "  [{i}] on {}: {}\n",
            format_name(&s.channel),
            to_source(&canonicalize(&s.reduct)),
        ));
    }
    let text_latex = match ns.repr() {
        Repr::Ascii => None,
        Repr::Latex => {
            let rows: Vec<String> = steps
                .iter()
                .map(|s| {
                    format!(
                        r"\text{{on }} {} & {}",
                        name_to_latex(&s.channel, None),
                        to_latex(&canonicalize(&s.reduct)),
                    )
                })
                .collect();
            Some(display_math(&format!(
                r"\begin{{array}}{{rl}}{}\end{{array}}",
                rows.join(r" \\ ")
            )))
        }
    };
    Ok(vec![MimeBundle {
        text_plain: plain,
        text_latex,
    }])
}

/// `#trace <ltsname>` samples a run from an LTS; `#trace <tracesname>[i]` shows
/// one enumerated trace's partial order.
fn dir_trace(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let arg = rest.trim();
    if arg.is_empty() {
        return arity_err("trace", "#trace <ltsname> | <tracesname>[i]");
    }
    // A `name[i]` handle selects one trace from a `#traces` set.
    if parse_index(arg).is_some() {
        let t = resolve_trace(arg, ns)?;
        return Ok(vec![render_trace(&t, ns.aliases(), ns.repr())]);
    }
    let lts = lookup_lts(arg, ns)?;
    // Follow the first outgoing transition from each state until a terminal
    // state or a repeat (guarding against cycles), bounded for safety.
    let mut run: Vec<(Name, usize)> = Vec::new();
    let mut current = lts.initial();
    let mut seen = vec![current];
    for _ in 0..lts.num_states().max(1) {
        let outgoing = lts.transitions(current);
        let Some(t) = outgoing.first() else { break };
        run.push((t.label.clone(), t.target));
        if seen.contains(&t.target) {
            break;
        }
        seen.push(t.target);
        current = t.target;
    }
    if run.is_empty() {
        return Ok(vec![MimeBundle::plain(
            "trace: the initial state is terminal (no transitions)",
        )]);
    }
    Ok(vec![render_run(
        "trace",
        &run,
        lts,
        ns.aliases(),
        ns.repr(),
    )])
}

/// `#traces <procname|inline DSL> [bound=N] -> name` — the trace-set.
fn dir_traces(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (pre, bind) = split_arrow(rest);
    let opts = Opts::parse(pre);
    let target = opts.target.trim();
    if target.is_empty() {
        return arity_err("traces", "#traces <procname|DSL> [bound=N] -> name");
    }
    let proc = resolve_proc(target, ns)?;
    let bound = opts.bound.unwrap_or(DEFAULT_BOUND);
    let (ts, truncated) = traces(&proc, bound, bound);
    let bundle = render_traces(&ts, truncated, ns.aliases(), ns.repr());
    if let Some(name) = bind {
        ns.insert(
            name,
            Obj::Traces {
                traces: ts,
                truncated,
            },
        );
    }
    Ok(vec![bundle])
}

/// `#lin <tracesname>[i]` — the linearizations of one trace, as label words.
fn dir_lin(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let t = resolve_trace(rest.trim(), ns)?;
    let lins: Vec<Vec<EventKey>> = t.linearizations().collect();
    let mut plain = format!("{} linearization(s):\n", lins.len());
    for (i, lin) in lins.iter().enumerate() {
        let word: Vec<String> = lin.iter().map(|e| fold_channel(&e.channel, ns)).collect();
        plain.push_str(&format!("  [{i}]  {}\n", word.join(" · ")));
    }
    Ok(vec![MimeBundle::plain(plain)])
}

/// `#project <tracesname>[i] <channel[,channel]>` — one agent's view of a trace:
/// the events on the named channels, under the induced causal order.
fn dir_project(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (spec, chans) = rest.trim().split_once(char::is_whitespace).ok_or_else(|| {
        CellError::new(
            "DirectiveError",
            "usage: #project <tracesname>[i] <channel[,channel]>",
        )
    })?;
    let t = resolve_trace(spec.trim(), ns)?;
    let names = resolve_names(&split_list(chans), ns)?;
    if names.is_empty() {
        return Err(CellError::new(
            "DirectiveError",
            "usage: #project <tracesname>[i] <channel[,channel]> — name at least one channel",
        ));
    }
    let projected = t.project(|e| names.iter().any(|n| name_equiv(&e.channel, n)));
    Ok(vec![render_trace(&projected, ns.aliases(), ns.repr())])
}

/// Fold a channel to its source alias for a listing, else its compact form.
fn fold_channel(name: &Name, ns: &Namespace) -> String {
    ns.aliases()
        .get(name)
        .map_or_else(|| format_name(name), str::to_string)
}

/// Parse a `name[i]` handle into `(name, i)`, or `None` if it is not one.
fn parse_index(spec: &str) -> Option<(&str, usize)> {
    let open = spec.find('[')?;
    let close = spec.find(']')?;
    if close != spec.len() - 1 || close < open {
        return None;
    }
    let name = spec[..open].trim();
    if !is_ident(name) {
        return None;
    }
    let idx: usize = spec[open + 1..close].trim().parse().ok()?;
    Some((name, idx))
}

/// Resolve a `name[i]` handle to the `i`-th trace of a `#traces` binding.
fn resolve_trace(spec: &str, ns: &Namespace) -> Result<Trace, CellError> {
    let spec = spec.trim();
    let (name, idx) = parse_index(spec).ok_or_else(|| {
        CellError::new(
            "TraceError",
            format!("expected a trace handle `name[i]`, got `{spec}`"),
        )
    })?;
    match ns.get(name) {
        Some(Obj::Traces { traces, .. }) => traces.get(idx).cloned().ok_or_else(|| {
            CellError::new(
                "IndexError",
                format!(
                    "`{name}` has {} trace(s); index {idx} is out of range",
                    traces.len()
                ),
            )
        }),
        Some(other) => Err(CellError::new(
            "NameError",
            format!("`{name}` is a {}, not a trace-set", other.kind()),
        )),
        None => Err(CellError::new(
            "NameError",
            format!("no trace-set named `{name}` (bind one with `#traces ... -> {name}`)"),
        )),
    }
}

/// `#typecheck <procname|inline DSL> [with a:Ty, b:Ty, ...]`
fn dir_typecheck(rest: &str, ns: &mut Namespace) -> Result<Vec<MimeBundle>, CellError> {
    let (target_src, env_src) = match split_on(rest, " with ") {
        Some((t, e)) => (t.trim(), Some(e.trim())),
        None => (rest.trim(), None),
    };
    if target_src.is_empty() {
        return arity_err("typecheck", "#typecheck <procname|DSL> [with a:Ty, ...]");
    }
    let proc = resolve_proc(target_src, ns)?;
    let env = match env_src {
        Some(src) => parse_env(src, ns)?,
        None => Env::new(),
    };
    let result = typecheck(&env, &proc);
    Ok(vec![render_typecheck(&result, ns.repr())])
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

/// Resolve a directive target: a bound proc name, else parse it as inline DSL
/// (absorbing any aliases so its names resolve in later cells).
fn resolve_proc(target: &str, ns: &mut Namespace) -> Result<Proc, CellError> {
    let target = target.trim();
    if is_ident(target) {
        if let Some(p) = ns.get_proc(target) {
            return Ok(p.clone());
        }
    }
    guard_nesting(target)?;
    let (proc, aliases) = parse_with_aliases(target).map_err(|e| parse_error(target, &e))?;
    ns.absorb_aliases(&proc, aliases);
    Ok(proc)
}

/// Look up a bound LTS by name, erroring clearly if it is missing or the wrong
/// kind.
fn lookup_lts<'a>(name: &str, ns: &'a Namespace) -> Result<&'a Lts, CellError> {
    lookup_lts_binding(name, ns).map(|(lts, _)| lts)
}

/// Look up a bound LTS together with the [`Reduction`] it was explored under.
fn lookup_lts_binding<'a>(
    name: &str,
    ns: &'a Namespace,
) -> Result<(&'a Lts, Reduction), CellError> {
    match ns.get(name) {
        Some(Obj::Lts { lts, reduction }) => Ok((lts, *reduction)),
        Some(other) => Err(CellError::new(
            "NameError",
            format!("`{name}` is a {}, not an lts", other.kind()),
        )),
        None => Err(CellError::new(
            "NameError",
            format!(
                "no LTS named `{name}` in this session (bind one with `#explore ... -> {name}`)"
            ),
        )),
    }
}

/// Reject an `EX` (next-time) formula against a reduced LTS: partial-order and
/// symmetry reduction do not preserve next-time, so such a verdict would be
/// silently wrong.
fn reject_ex_on_reduced(
    compiled: &crate::formula::CompiledFormula,
    reduction: Reduction,
) -> Result<(), CellError> {
    if compiled.uses_ex && reduction != Reduction::None {
        Err(CellError::new(
            "ReductionError",
            format!(
                "this LTS is {} — the `EX` (next-time) modality is not preserved \
                 under reduction, so the verdict would be unsound. Re-explore with \
                 plain `#explore` (no `por` / `sym=`) to check next-time properties.",
                reduction.label()
            ),
        ))
    } else {
        Ok(())
    }
}

/// Attach a reduction caveat to a rendered bundle (a no-op for a full LTS), so a
/// verdict against a reduced LTS is never presented without its soundness
/// qualification.
fn apply_caveat(mut bundle: MimeBundle, reduction: Reduction) -> MimeBundle {
    if let Some(caveat) = reduction.caveat() {
        bundle.text_plain = format!("{}\n[caveat] {caveat}", bundle.text_plain);
        // The caveat must ride along with the LaTeX view too, so a MathJax
        // front-end never shows a reduced verdict without its qualification.
        if let Some(latex) = &bundle.text_latex {
            let note = display_math(&format!(
                r"\text{{caveat: {}}}",
                crate::render::escape_latex_text(caveat)
            ));
            bundle.text_latex = Some(format!("{latex}\n{note}"));
        }
    }
    bundle
}

/// Compile a formula against the namespace's name table, mapping a formula error
/// to a span-aware [`CellError`].
fn compile_formula(
    src: &str,
    ns: &Namespace,
) -> Result<crate::formula::CompiledFormula, CellError> {
    let resolve = |ident: &str| ns.resolve_name(ident);
    parse_formula(src, &resolve).map_err(|e| {
        let caret = caret_line(src, e.column);
        CellError::with_traceback(
            "FormulaError",
            e.to_string(),
            vec![src.to_string(), caret, e.to_string()],
        )
    })
}

/// Resolve a list of surface identifiers to canonical channel names.
fn resolve_names(idents: &[String], ns: &Namespace) -> Result<Vec<Name>, CellError> {
    idents
        .iter()
        .map(|id| {
            ns.resolve_name(id).ok_or_else(|| {
                CellError::new(
                    "NameError",
                    format!("unknown channel `{id}` — not a name defined in this session"),
                )
            })
        })
        .collect()
}

/// Parse a minimal typing environment: `a:Ty, b:Ty, ...` where `Ty` is `Nil`,
/// `Proc`, or `Chan(Ty)`. Channel names resolve via the namespace.
fn parse_env(src: &str, ns: &Namespace) -> Result<Env, CellError> {
    // `parse_ty` recurses on `Chan(..)`; bound its depth up front.
    guard_nesting(src)?;
    let mut env = Env::new();
    for entry in src.split(',') {
        let entry = entry.trim();
        if entry.is_empty() {
            continue;
        }
        let (name, ty_src) = entry.split_once(':').ok_or_else(|| {
            CellError::new(
                "TypeEnvError",
                format!("bad Γ entry `{entry}` — expected `name:Ty`"),
            )
        })?;
        let name = name.trim();
        let chan = ns.resolve_name(name).ok_or_else(|| {
            CellError::new(
                "NameError",
                format!("unknown channel `{name}` in Γ — define it in a DSL cell first"),
            )
        })?;
        let ty = parse_ty(ty_src.trim())?;
        env = env.with(chan, ty);
    }
    Ok(env)
}

fn parse_ty(src: &str) -> Result<Ty, CellError> {
    let src = src.trim();
    match src {
        "Nil" => Ok(Ty::Nil),
        "Proc" => Ok(Ty::Proc),
        _ => {
            if let Some(inner) = src.strip_prefix("Chan(").and_then(|s| s.strip_suffix(')')) {
                Ok(Ty::chan(parse_ty(inner)?))
            } else {
                Err(CellError::new(
                    "TypeError",
                    format!("bad type `{src}` — expected Nil, Proc, or Chan(<Ty>)"),
                ))
            }
        }
    }
}

/// Directive options parsed off a directive body: the residual `target` string
/// plus recognised flags.
#[derive(Default)]
struct Opts {
    target: String,
    bound: Option<usize>,
    por: bool,
    weak: bool,
    obs: Vec<String>,
    sym: Vec<String>,
}

impl Opts {
    fn parse(input: &str) -> Self {
        let mut opts = Opts::default();
        let mut target_words: Vec<&str> = Vec::new();
        for word in input.split_whitespace() {
            if word == "por" {
                opts.por = true;
            } else if word == "weak" {
                opts.weak = true;
            } else if let Some(n) = word.strip_prefix("bound=") {
                opts.bound = n.parse().ok();
            } else if let Some(list) = word.strip_prefix("obs=") {
                opts.obs = split_list(list);
            } else if let Some(list) = word.strip_prefix("sym=") {
                opts.sym = split_list(list);
            } else {
                target_words.push(word);
            }
        }
        opts.target = target_words.join(" ");
        opts
    }
}

fn split_list(s: &str) -> Vec<String> {
    s.split(',')
        .map(str::trim)
        .filter(|t| !t.is_empty())
        .map(str::to_string)
        .collect()
}

/// Split a directive body at a trailing `-> name` binding arrow.
fn split_arrow(s: &str) -> (&str, Option<String>) {
    match s.rfind("->") {
        Some(idx) => {
            let name = s[idx + 2..].trim();
            if is_ident(name) {
                (&s[..idx], Some(name.to_string()))
            } else {
                (s, None)
            }
        }
        None => (s, None),
    }
}

/// Split a string on the first occurrence of `sep`.
fn split_on<'a>(s: &'a str, sep: &str) -> Option<(&'a str, &'a str)> {
    s.find(sep).map(|i| (&s[..i], &s[i + sep.len()..]))
}

/// Split off the first whitespace-delimited word, returning `(word, rest)`.
fn split_first_word(s: &str) -> (&str, &str) {
    let s = s.trim_start();
    match s.find(char::is_whitespace) {
        Some(i) => (&s[..i], &s[i..]),
        None => (s, ""),
    }
}

/// Whether `s` is a single DSL identifier (`[A-Za-z_][A-Za-z0-9_]*`).
pub(crate) fn is_ident(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_alphanumeric() || c == '_')
}

fn arity_err(name: &str, usage: &str) -> Result<Vec<MimeBundle>, CellError> {
    Err(CellError::new(
        "DirectiveError",
        format!("`#{name}` — usage: {usage}"),
    ))
}

/// Convert a [`ParseError`] into a span-aware [`CellError`] with a caret line.
fn parse_error(src: &str, e: &ParseError) -> CellError {
    let line = src.lines().nth(e.line.saturating_sub(1)).unwrap_or("");
    let caret = caret_line(line, e.column);
    CellError::with_traceback(
        "ParseError",
        e.to_string(),
        vec![line.to_string(), caret, e.to_string()],
    )
}

/// A caret line pointing at 1-based `column`.
fn caret_line(_line: &str, column: usize) -> String {
    let pad = column.saturating_sub(1);
    format!("{}^", " ".repeat(pad))
}

/// The `#help` display listing the notebook vocabulary.
fn help_bundle() -> MimeBundle {
    let plain = "\
Stratum notebook cells:
  DSL cell         Stratum code; binds to an auto name (`_1`, `_2`, ...)
  #define <name>   bind this cell's process to <name> (code below, or inline)
  #explore <p> [bound=N] [por] [obs=a,b] [sym=a,b] -> lts   build the trace LTS
  #expand <p>                                    show the desugared pure core
  #check <formula> on <lts>                      model-check (holds + exact)
  #witness <formula> on <lts>                    a run reaching the goal
  #counterexample <invariant> on <lts>           a run violating the invariant
  #bisim <p> <q> [weak] [obs=a,b]                barbed (bi)simulation verdict
  #step <p>                                       one-step reducts
  #traces <p> [bound=N] -> tr                    the trace-set (partial orders)
  #trace <lts> | tr[i]                            a sample run, or trace tr[i]
  #lin tr[i]                                      linearizations of trace tr[i]
  #project tr[i] <a,b>                            one agent's view of trace tr[i]
  #typecheck <p> [with a:Ty, b:Ty]               channel-sort typecheck
  #rune <newline> <script>                       run an embedded Rune script
  #ascii / #latex                                output representation (`#repr` shows current)
  #help                                           this list

#define: `#define hs` on its own line names the process built from the Stratum
code on the lines below; `#define e @0!(0)` binds an inline one-liner.

Output: every result is a copyable ASCII listing. `#latex` additionally emits a
`text/latex` view in classic reflective rho-calculus notation (a MathJax
front-end typesets it, copyable as source or image); `#ascii` (the default)
switches back to plain listings only. Processes render as their surface form —
`#expand <p>` shows the desugared pure core on demand.

#rune: the rest of the cell is a Rune script (an implicit `pub fn main()`) with
a curated `stratum` module bound in and this session's bindings shared. Free fns:
stratum::parse(src) -> proc; stratum::explore(p, bound) / explore_por / _symmetric
-> lts; stratum::check(lts, formula) -> bool (same formula language as #check);
stratum::witness / counterexample(lts, f) -> [state indices]; stratum::bisim(p, q,
weak) -> verdict; stratum::get(name) / set(name, value) read / write bindings.
`println!(...)` is captured as the cell's stdout; the final expression is the
display. A runaway Rune loop trips a per-instruction budget and errors cleanly;
the budget does NOT bound work inside a single native call (a big explore/check/
bisim is limited only by its own arguments, e.g. the exploration state cap).

Formula fragment: EF/AG/AF/EG/EX φ, φ & ψ, φ | ψ, !φ, ( ), and the atomic
proposition emits(<name>) — a top-level OUTPUT barb on the named channel.
Types: Nil, Proc, Chan(<Ty>).

Reduced LTSs (`#explore ... por` / `sym=...`) preserve only a fragment of
the logic: `#check`/`#witness`/`#counterexample` REJECT the `EX` (next-time)
modality on them, and other verdicts carry a caveat. Use plain `#explore`
(no por/sym) to check next-time properties.";
    MimeBundle::plain(plain)
}
