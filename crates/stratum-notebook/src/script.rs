//! The `#rune` cell: an embedded [Rune] scripting engine with a curated,
//! faithful `stratum` module bound in and the session [`Namespace`] shared.
//!
//! [Rune]: https://rune-rs.github.io/
//!
//! A `#rune` cell lets a researcher script loops and custom algorithms over the
//! *real* toolkit objects — the same [`stratum::core::Proc`] /
//! [`stratum::lts::Lts`] / [`stratum::equiv::Verdict`] values created in earlier
//! DSL / directive cells — without recompiling the kernel. Every function in the
//! bound module calls straight through to the toolkit, so a script's answer is
//! exactly what the corresponding directive would produce.
//!
//! ## Scripting API
//!
//! The cell body is compiled as the body of an implicit `pub fn main()` (unless
//! it already defines an `fn main`), so a cell is just a sequence of statements.
//! `println!(...)` is captured into the cell's stdout; the value of the final
//! expression is rendered like any other cell result.
//!
//! Free functions in the `stratum` module (each faithfully calls the toolkit):
//!
//! ```rune
//! let p = stratum::parse("new a\na!(0) | a(x).0");  // ScProc
//! let lts = stratum::explore(p, 100);               // ScLts
//! let ok = stratum::check(lts, "EF emits(a)");      // bool
//! let v = stratum::bisim(p, p, false);              // ScVerdict
//! stratum::set("result", lts);                      // write back to the session
//! let earlier = stratum::get("myproc");             // read a prior binding
//! ```
//!
//! * `parse(src) -> ScProc` — parse the surface DSL (no implicit stdlib).
//! * `explore(p, bound) -> ScLts`, `explore_por(p, bound, [chans])`,
//!   `explore_symmetric(p, bound, [chans])` — build the trace LTS. Channel names
//!   in the lists are resolved against the session namespace.
//! * `check(lts, formula) -> bool` (alias `holds`) — model-check, using the very
//!   same formula sub-language as the `#check` directive.
//! * `witness(lts, formula) -> Vec<i64>` / `counterexample(lts, inv) -> Vec<i64>`
//!   — the state indices along a witnessing / violating run (empty if none).
//! * `bisim(p, q, weak) -> ScVerdict` — barbed (bi)simulation verdict.
//! * `get(name) -> value` / `set(name, value)` — read / write a session binding.
//!
//! Wrapper methods:
//!
//! * `ScProc`: `.expand()`, `.source()`, `.is_normal_form()`, `.step()`,
//!   `.free_name_count()`, `.quote_depth()`.
//! * `ScLts`: `.num_states()`, `.num_transitions()`, `.is_truncated()`,
//!   `.initial()`, `.state(i)`, `.successors(i)`, `.to_dot()`.
//! * `ScVerdict`: `.is_equivalent()`, `.to_string()`.
//!
//! ## Safety
//!
//! The VM runs under a per-instruction [budget](RUNE_BUDGET); a runaway *Rune*
//! loop exhausts the budget and surfaces a clean `RuneBudgetError` instead of
//! hanging the kernel. Compile and runtime errors become clean [`CellError`]s
//! (with Rune's own diagnostics formatted into the traceback); nothing here
//! panics.
//!
//! The budget counts Rune VM instructions only — it does **not** bound work
//! *inside* a native call. A single `explore(p, huge_bound)` / `check(...)` /
//! `bisim(...)` is one instruction as far as the budget is concerned, so its
//! cost is governed solely by its own arguments (e.g. the exploration state
//! cap), not by the budget. The budget protects against runaway *scripting*
//! (loops, recursion), not against an expensive single toolkit call.

use std::sync::{Arc, Mutex};

use rune::modules::capture_io::{self, CaptureIo};
use rune::runtime::{budget, Value, VmResult};
use rune::termcolor::Buffer;
use rune::{Any, Context, ContextError, Diagnostics, Module, Source, Sources, Vm};

use stratum::core::{canonicalize, is_normal_form, step, Name, Proc};
use stratum::equiv::{strong_barbed_bisimilar, weak_barbed_bisimilar, Verdict};
use stratum::logic::{counterexample, holds_checked, witness};
use stratum::lts::Lts;
use stratum::syntax::{parse_with_aliases, to_source};

use crate::formula::parse_formula;
use crate::render::{render_lts, render_proc, render_verdict, MimeBundle};
use crate::{CellError, CellOutcome, Namespace, Obj, Reduction};

/// The default per-instruction execution budget for a `#rune` cell.
///
/// Budgeting in Rune is per-VM-instruction (see [`rune::runtime::budget`]); a
/// script that exhausts this cap halts with a clean error rather than hanging
/// the kernel. Ten million instructions is generous for the loops a researcher
/// writes over an explored LTS, yet a tight infinite loop trips it in well under
/// a second.
pub const RUNE_BUDGET: usize = 10_000_000;

/// The default bounded-exploration state cap for scripted `bisim` (mirrors the
/// `#bisim` directive default so a scripted verdict matches the directive's).
const DEFAULT_SCRIPT_BOUND: usize = 1000;

/// A shared handle to the session namespace, captured by the `get` / `set`
/// module functions so a script reads and writes the *same* bindings the cell is
/// evaluating against.
type SharedNs = Arc<Mutex<Namespace>>;

/// Lock the shared namespace, recovering from a poisoned mutex (a native
/// function can only poison it by unwinding, which our functions never do — this
/// is defensive).
fn lock(ns: &SharedNs) -> std::sync::MutexGuard<'_, Namespace> {
    ns.lock().unwrap_or_else(|e| e.into_inner())
}

// ---------------------------------------------------------------------------
// Wrapper types (orphan rule): thin newtypes over foreign toolkit values.
// ---------------------------------------------------------------------------

/// A process, wrapping [`stratum::core::Proc`] for Rune.
#[derive(Any, Clone)]
#[rune(item = ::stratum)]
pub struct ScProc(Proc);

/// A trace LTS with the reduction it was explored under, wrapping
/// [`stratum::lts::Lts`] for Rune.
#[derive(Any, Clone)]
#[rune(item = ::stratum)]
pub struct ScLts {
    lts: Lts,
    reduction: Reduction,
}

/// An equivalence verdict, wrapping [`stratum::equiv::Verdict`] for Rune.
#[derive(Any, Clone)]
#[rune(item = ::stratum)]
pub struct ScVerdict(Verdict);

impl ScProc {
    fn expand(&self) -> String {
        to_source(&canonicalize(&self.0))
    }
    fn source(&self) -> String {
        to_source(&self.0)
    }
    fn is_normal_form(&self) -> bool {
        is_normal_form(&self.0)
    }
    fn step(&self) -> Vec<ScProc> {
        step(&self.0).into_iter().map(ScProc).collect()
    }
    fn free_name_count(&self) -> i64 {
        self.0.free_vars().len() as i64
    }
    fn quote_depth(&self) -> i64 {
        self.0.quote_depth() as i64
    }
}

impl ScLts {
    fn state(&self, i: i64) -> VmResult<ScProc> {
        match usize::try_from(i) {
            Ok(idx) if idx < self.lts.num_states() => {
                VmResult::Ok(ScProc(self.lts.state(idx).clone()))
            }
            _ => VmResult::panic(format!(
                "state index {i} out of range (LTS has {} states)",
                self.lts.num_states()
            )),
        }
    }
    fn successors(&self, i: i64) -> VmResult<Vec<i64>> {
        match usize::try_from(i) {
            Ok(idx) if idx < self.lts.num_states() => VmResult::Ok(
                self.lts
                    .transitions(idx)
                    .iter()
                    .map(|t| t.target as i64)
                    .collect(),
            ),
            _ => VmResult::panic(format!(
                "state index {i} out of range (LTS has {} states)",
                self.lts.num_states()
            )),
        }
    }
}

// ---------------------------------------------------------------------------
// The `stratum` module.
// ---------------------------------------------------------------------------

/// Build the `stratum` Rune module: the wrapper types, their methods, and the
/// curated free functions, all closing over the shared session namespace.
fn stratum_module(shared: &SharedNs) -> Result<Module, ContextError> {
    let mut m = Module::with_crate("stratum")?;

    // Types.
    m.ty::<ScProc>()?;
    m.ty::<ScLts>()?;
    m.ty::<ScVerdict>()?;

    // ScProc methods.
    m.associated_function("expand", ScProc::expand)?;
    m.associated_function("source", ScProc::source)?;
    m.associated_function("is_normal_form", ScProc::is_normal_form)?;
    m.associated_function("step", ScProc::step)?;
    m.associated_function("free_name_count", ScProc::free_name_count)?;
    m.associated_function("quote_depth", ScProc::quote_depth)?;

    // ScLts methods.
    m.associated_function("num_states", |l: &ScLts| l.lts.num_states() as i64)?;
    m.associated_function("num_transitions", |l: &ScLts| {
        l.lts.num_transitions() as i64
    })?;
    m.associated_function("is_truncated", |l: &ScLts| l.lts.is_truncated())?;
    m.associated_function("initial", |l: &ScLts| l.lts.initial() as i64)?;
    m.associated_function("state", ScLts::state)?;
    m.associated_function("successors", ScLts::successors)?;
    m.associated_function("to_dot", |l: &ScLts| l.lts.to_dot())?;

    // ScVerdict methods.
    m.associated_function("is_equivalent", |v: &ScVerdict| v.0.is_equivalent())?;
    m.associated_function("to_string", |v: &ScVerdict| verdict_string(&v.0))?;

    // Free functions.
    m.function("parse", |src: &str| fn_parse(src)).build()?;

    m.function("explore", |p: &ScProc, bound: i64| fn_explore(p, bound))
        .build()?;

    {
        let ns = shared.clone();
        m.function(
            "explore_por",
            move |p: &ScProc, bound: i64, obs: Vec<String>| fn_explore_por(&ns, p, bound, &obs),
        )
        .build()?;
    }
    {
        let ns = shared.clone();
        m.function(
            "explore_symmetric",
            move |p: &ScProc, bound: i64, inter: Vec<String>| {
                fn_explore_symmetric(&ns, p, bound, &inter)
            },
        )
        .build()?;
    }

    {
        let ns = shared.clone();
        m.function("check", move |l: &ScLts, formula: &str| {
            fn_check(&ns, l, formula)
        })
        .build()?;
    }
    {
        let ns = shared.clone();
        m.function("holds", move |l: &ScLts, formula: &str| {
            fn_check(&ns, l, formula)
        })
        .build()?;
    }
    {
        let ns = shared.clone();
        m.function("witness", move |l: &ScLts, formula: &str| {
            fn_run(&ns, l, formula, false)
        })
        .build()?;
    }
    {
        let ns = shared.clone();
        m.function("counterexample", move |l: &ScLts, inv: &str| {
            fn_run(&ns, l, inv, true)
        })
        .build()?;
    }

    m.function("bisim", |p: &ScProc, q: &ScProc, weak: bool| {
        fn_bisim(p, q, weak)
    })
    .build()?;

    {
        let ns = shared.clone();
        m.function("get", move |name: &str| fn_get(&ns, name))
            .build()?;
    }
    {
        let ns = shared.clone();
        m.function("set", move |name: &str, value: Value| {
            fn_set(&ns, name, value)
        })
        .build()?;
    }

    Ok(m)
}

// ---------------------------------------------------------------------------
// Free-function implementations — each calls the real toolkit.
// ---------------------------------------------------------------------------

fn fn_parse(src: &str) -> VmResult<ScProc> {
    match parse_with_aliases(src) {
        Ok((proc, _aliases)) => VmResult::Ok(ScProc(proc)),
        Err(e) => VmResult::panic(format!("parse error: {e}")),
    }
}

fn to_bound(bound: i64) -> Result<usize, VmResult<ScLts>> {
    usize::try_from(bound).map_err(|_| VmResult::panic(format!("bound {bound} must be >= 0")))
}

fn fn_explore(p: &ScProc, bound: i64) -> VmResult<ScLts> {
    let bound = match to_bound(bound) {
        Ok(b) => b,
        Err(e) => return e,
    };
    VmResult::Ok(ScLts {
        lts: Lts::explore(&p.0, bound),
        reduction: Reduction::None,
    })
}

fn fn_explore_por(ns: &SharedNs, p: &ScProc, bound: i64, obs: &[String]) -> VmResult<ScLts> {
    let bound = match to_bound(bound) {
        Ok(b) => b,
        Err(e) => return e,
    };
    let observed = match resolve_channels(ns, obs) {
        Ok(v) => v,
        Err(msg) => return VmResult::panic(msg),
    };
    VmResult::Ok(ScLts {
        lts: Lts::explore_por(&p.0, bound, &observed),
        reduction: Reduction::Por,
    })
}

fn fn_explore_symmetric(
    ns: &SharedNs,
    p: &ScProc,
    bound: i64,
    inter: &[String],
) -> VmResult<ScLts> {
    let bound = match to_bound(bound) {
        Ok(b) => b,
        Err(e) => return e,
    };
    let interchangeable = match resolve_channels(ns, inter) {
        Ok(v) => v,
        Err(msg) => return VmResult::panic(msg),
    };
    VmResult::Ok(ScLts {
        lts: Lts::explore_symmetric(&p.0, bound, &interchangeable),
        reduction: Reduction::Symmetry,
    })
}

fn fn_check(ns: &SharedNs, l: &ScLts, formula: &str) -> VmResult<bool> {
    let compiled = {
        let ns = lock(ns);
        parse_formula(formula, &|id| ns.resolve_name(id))
    };
    let compiled = match compiled {
        Ok(c) => c,
        Err(e) => return VmResult::panic(format!("formula error: {e}")),
    };
    if compiled.uses_ex && l.reduction != Reduction::None {
        return VmResult::panic(format!(
            "this LTS is {} — the `EX` (next-time) modality is not preserved under \
             reduction, so the verdict would be unsound",
            l.reduction.label()
        ));
    }
    let label = compiled.labelling();
    VmResult::Ok(holds_checked(&l.lts, &compiled.formula, &label).holds)
}

fn fn_run(ns: &SharedNs, l: &ScLts, formula: &str, counter: bool) -> VmResult<Vec<i64>> {
    let compiled = {
        let ns = lock(ns);
        parse_formula(formula, &|id| ns.resolve_name(id))
    };
    let compiled = match compiled {
        Ok(c) => c,
        Err(e) => return VmResult::panic(format!("formula error: {e}")),
    };
    if compiled.uses_ex && l.reduction != Reduction::None {
        return VmResult::panic(format!(
            "this LTS is {} — the `EX` (next-time) modality is not preserved under reduction",
            l.reduction.label()
        ));
    }
    let label = compiled.labelling();
    let run = if counter {
        counterexample(&l.lts, &compiled.formula, &label)
    } else {
        witness(&l.lts, &compiled.formula, &label)
    };
    VmResult::Ok(
        run.map(|steps| steps.iter().map(|(_, s)| *s as i64).collect())
            .unwrap_or_default(),
    )
}

fn fn_bisim(p: &ScProc, q: &ScProc, weak: bool) -> VmResult<ScVerdict> {
    let obs = crate::default_observations(&p.0, &q.0);
    let bound = DEFAULT_SCRIPT_BOUND;
    let verdict = if weak {
        weak_barbed_bisimilar(&p.0, &q.0, &obs, bound)
    } else {
        strong_barbed_bisimilar(&p.0, &q.0, &obs, bound)
    };
    VmResult::Ok(ScVerdict(verdict))
}

fn fn_get(ns: &SharedNs, name: &str) -> VmResult<Value> {
    let ns = lock(ns);
    let obj = match ns.get(name) {
        Some(o) => o,
        None => return VmResult::panic(format!("no object named `{name}` in this session")),
    };
    let converted = match obj {
        Obj::Proc(p) => rune::to_value(ScProc(p.clone())),
        Obj::Lts { lts, reduction } => rune::to_value(ScLts {
            lts: lts.clone(),
            reduction: *reduction,
        }),
        Obj::Verdict(v) => rune::to_value(ScVerdict(v.clone())),
        Obj::Checked(c) => rune::to_value(c.holds),
        Obj::Bool(b) => rune::to_value(*b),
        Obj::Int(i) => rune::to_value(*i),
        Obj::Text(t) => rune::to_value(t.clone()),
    };
    match converted {
        Ok(v) => VmResult::Ok(v),
        Err(e) => VmResult::panic(format!("could not expose `{name}` to the script: {e}")),
    }
}

fn fn_set(ns: &SharedNs, name: &str, value: Value) -> VmResult<()> {
    let obj = if let Ok(p) = rune::from_value::<ScProc>(value.clone()) {
        Obj::Proc(p.0)
    } else if let Ok(l) = rune::from_value::<ScLts>(value.clone()) {
        Obj::Lts {
            lts: l.lts,
            reduction: l.reduction,
        }
    } else if let Ok(v) = rune::from_value::<ScVerdict>(value.clone()) {
        Obj::Verdict(v.0)
    } else if let Ok(b) = rune::from_value::<bool>(value.clone()) {
        Obj::Bool(b)
    } else if let Ok(i) = rune::from_value::<i64>(value.clone()) {
        Obj::Int(i)
    } else if let Ok(s) = rune::from_value::<String>(value.clone()) {
        Obj::Text(s)
    } else {
        return VmResult::panic(format!(
            "cannot `set(\"{name}\", …)`: value is not a proc, lts, verdict, bool, int, or string"
        ));
    };
    lock(ns).insert(name.to_string(), obj);
    VmResult::Ok(())
}

/// Resolve surface channel identifiers against the session namespace.
fn resolve_channels(ns: &SharedNs, idents: &[String]) -> Result<Vec<Name>, String> {
    let ns = lock(ns);
    idents
        .iter()
        .map(|id| {
            ns.resolve_name(id)
                .ok_or_else(|| format!("unknown channel `{id}` — not defined in this session"))
        })
        .collect()
}

fn verdict_string(v: &Verdict) -> String {
    match v {
        Verdict::Equivalent => "Equivalent".to_string(),
        Verdict::Distinguished(r) => format!("Distinguished: {r}"),
        Verdict::Inconclusive(r) => format!("Inconclusive: {r}"),
    }
}

// ---------------------------------------------------------------------------
// Engine entry point.
// ---------------------------------------------------------------------------

/// Run a `#rune` cell body against the session namespace, returning the cell's
/// captured stdout, an optional rendered return value, and any error — all as a
/// [`CellOutcome`].
///
/// The namespace is moved into a shared handle for the duration of the script so
/// the bound `get` / `set` functions read and write the same bindings, then
/// moved back. Nothing here panics: compile / runtime / budget failures all
/// become structured [`CellError`]s.
pub(crate) fn run_rune(body: &str, ns: &mut Namespace) -> CellOutcome {
    // Move the namespace into a shared handle the module functions can reach.
    let shared: SharedNs = Arc::new(Mutex::new(std::mem::take(ns)));

    // `mem::take` above left the caller's namespace defaulted (empty). Restore it
    // via a Drop guard so the write-back happens on EVERY exit path — including a
    // Rust unwind out of `run_inner` (which the kernel's `catch_unwind` would
    // otherwise turn into an error reply *with the whole session already wiped*).
    // Cloning back is robust regardless of any lingering Arc reference count.
    let _restore = NsRestore {
        ns,
        shared: shared.clone(),
    };

    let io = CaptureIo::new();
    let (display, error) = run_inner(body, &shared, &io);

    // Drain captured stdout.
    let mut buf: Vec<u8> = Vec::new();
    let _ = io.drain_into(&mut buf);
    let stream_stdout = String::from_utf8_lossy(&buf).into_owned();

    CellOutcome {
        displays: display.into_iter().collect(),
        stream_stdout,
        error,
    }
    // `_restore` drops here (or during an unwind), writing `shared` back into the
    // caller's `&mut Namespace`.
}

/// Drop guard that writes the shared session namespace back into the caller's
/// `&mut Namespace` when it drops — on the normal path, the error path, and
/// during an unwind — so a mid-script panic can never leave the session wiped by
/// the `mem::take` in [`run_rune`].
struct NsRestore<'a> {
    ns: &'a mut Namespace,
    shared: SharedNs,
}

impl Drop for NsRestore<'_> {
    fn drop(&mut self) {
        *self.ns = lock(&self.shared).clone();
    }
}

/// Compile and run the script, returning `(rendered return value, error)`.
fn run_inner(
    body: &str,
    shared: &SharedNs,
    io: &CaptureIo,
) -> (Option<MimeBundle>, Option<CellError>) {
    // Build the context: default modules WITHOUT real stdio, plus the capture-io
    // module (so `println!` is captured) and our curated `stratum` module.
    let context = match build_context(shared, io) {
        Ok(c) => c,
        Err(e) => {
            return (
                None,
                Some(CellError::new(
                    "RuneSetupError",
                    format!("failed to build the rune context: {e}"),
                )),
            )
        }
    };
    let runtime = match context.runtime() {
        Ok(r) => Arc::new(r),
        Err(e) => {
            return (
                None,
                Some(CellError::new(
                    "RuneSetupError",
                    format!("failed to build the rune runtime: {e}"),
                )),
            )
        }
    };

    // Wrap the cell body as the body of an implicit `pub fn main()` unless the
    // user defines their own `fn main` item.
    let program = if defines_main(body) {
        body.to_string()
    } else {
        format!("pub fn main() {{\n{body}\n}}\n")
    };

    let mut sources = Sources::new();
    let source = match Source::new("cell", &program) {
        Ok(s) => s,
        Err(e) => {
            return (
                None,
                Some(CellError::new("RuneSetupError", format!("bad source: {e}"))),
            )
        }
    };
    if sources.insert(source).is_err() {
        return (
            None,
            Some(CellError::new(
                "RuneSetupError",
                "failed to register source",
            )),
        );
    }

    let mut diagnostics = Diagnostics::new();
    let unit = match rune::prepare(&mut sources)
        .with_context(&context)
        .with_diagnostics(&mut diagnostics)
        .build()
    {
        Ok(unit) => unit,
        Err(_) => {
            let text = emit_diagnostics(&diagnostics, &sources);
            return (None, Some(compile_error(text)));
        }
    };

    let mut vm = Vm::new(runtime, Arc::new(unit));

    // Run `main` under a per-instruction budget so a runaway loop errors instead
    // of hanging.
    let result = budget::with(RUNE_BUDGET, || vm.call(["main"], ())).call();

    match result {
        Ok(value) => (render_value(&value, shared), None),
        Err(e) => {
            let msg = e.to_string();
            if msg.contains("limited") {
                (
                    None,
                    Some(CellError::new(
                        "RuneBudgetError",
                        format!(
                            "instruction budget exceeded (limit {RUNE_BUDGET}) — the script was \
                             halted so it could not hang the kernel. Reduce the work per cell or \
                             lower an exploration bound."
                        ),
                    )),
                )
            } else {
                let mut buf = Buffer::no_color();
                let _ = e.emit(&mut buf, &sources);
                let detail = String::from_utf8_lossy(buf.as_slice()).into_owned();
                (None, Some(runtime_error(&msg, detail)))
            }
        }
    }
}

/// Build the Rune [`Context`] for a `#rune` cell.
fn build_context(shared: &SharedNs, io: &CaptureIo) -> Result<Context, ContextError> {
    // `with_config(false)` installs the default modules but omits real stdio, so
    // the capture-io module owns `print` / `println`.
    let mut context = Context::with_config(false)?;
    context.install(capture_io::module(io)?)?;
    context.install(stratum_module(shared)?)?;
    Ok(context)
}

/// Format Rune build diagnostics into a plain string (no ANSI colour).
fn emit_diagnostics(diagnostics: &Diagnostics, sources: &Sources) -> String {
    let mut buf = Buffer::no_color();
    let _ = diagnostics.emit(&mut buf, sources);
    String::from_utf8_lossy(buf.as_slice()).into_owned()
}

/// A compile error, with the emitted diagnostics as the traceback.
fn compile_error(text: String) -> CellError {
    let first = text
        .lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("rune compile error")
        .to_string();
    let traceback = text.lines().map(str::to_string).collect::<Vec<_>>();
    CellError::with_traceback(
        "RuneCompileError",
        strip_prefix(&first),
        if traceback.is_empty() {
            vec![first]
        } else {
            traceback
        },
    )
}

/// A runtime error, formatted from the VM error message plus emitted diagnostics.
fn runtime_error(msg: &str, detail: String) -> CellError {
    let evalue = strip_prefix(msg);
    let traceback = if detail.trim().is_empty() {
        vec![evalue.clone()]
    } else {
        detail.lines().map(str::to_string).collect()
    };
    CellError::with_traceback("RuneRuntimeError", evalue, traceback)
}

/// Strip Rune's `Panicked: ` prefix from a native-function error message so the
/// researcher sees just the domain message.
fn strip_prefix(msg: &str) -> String {
    msg.strip_prefix("Panicked: ").unwrap_or(msg).to_string()
}

/// Render a script's final value into a [`MimeBundle`], or `None` for unit /
/// no-value cells.
fn render_value(value: &Value, shared: &SharedNs) -> Option<MimeBundle> {
    // Unit → no display.
    if rune::from_value::<()>(value.clone()).is_ok() {
        return None;
    }
    if let Ok(l) = rune::from_value::<ScLts>(value.clone()) {
        return Some(render_sclts(&l));
    }
    if let Ok(p) = rune::from_value::<ScProc>(value.clone()) {
        let aliases = lock(shared).aliases().clone();
        return Some(render_proc(&p.0, &aliases));
    }
    if let Ok(v) = rune::from_value::<ScVerdict>(value.clone()) {
        return Some(render_verdict(&v.0));
    }
    if let Ok(b) = rune::from_value::<bool>(value.clone()) {
        return Some(MimeBundle::plain(b.to_string()));
    }
    if let Ok(i) = rune::from_value::<i64>(value.clone()) {
        return Some(MimeBundle::plain(i.to_string()));
    }
    if let Ok(f) = rune::from_value::<f64>(value.clone()) {
        return Some(MimeBundle::plain(f.to_string()));
    }
    if let Ok(s) = rune::from_value::<String>(value.clone()) {
        return Some(MimeBundle::plain(s));
    }
    Some(MimeBundle::plain(format!("{value:?}")))
}

/// Render an [`ScLts`] return value, appending the reduction caveat if any.
fn render_sclts(l: &ScLts) -> MimeBundle {
    let mut bundle = render_lts(&l.lts);
    if let Some(caveat) = l.reduction.caveat() {
        bundle.text_plain = format!("{}\n[caveat] {caveat}", bundle.text_plain);
    }
    bundle
}

/// Whether the script defines its own `fn main` *item* (so we must not wrap it).
///
/// Token-aware, to avoid the false positive of the literal text `fn main`
/// appearing inside a string or comment (e.g. `let s = "fn main";`): comments
/// and string / char literals are blanked out first, then we look for two
/// adjacent identifier tokens `fn` `main`.
fn defines_main(body: &str) -> bool {
    let code = blank_strings_and_comments(body);
    let mut prev = "";
    for word in code.split(|c: char| !(c.is_alphanumeric() || c == '_')) {
        if word.is_empty() {
            continue;
        }
        if prev == "fn" && word == "main" {
            return true;
        }
        prev = word;
    }
    false
}

/// Replace the contents of comments and string / char literals with spaces so a
/// downstream token scan never trips over code-looking text inside them. A
/// lightweight, non-nesting heuristic — good enough to gate the `main` wrapper.
fn blank_strings_and_comments(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let mut chars = src.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '/' if chars.peek() == Some(&'/') => {
                // Line comment: drop to (and keep) the newline.
                for c2 in chars.by_ref() {
                    if c2 == '\n' {
                        out.push('\n');
                        break;
                    }
                }
            }
            '/' if chars.peek() == Some(&'*') => {
                // Block comment: drop to the closing `*/`.
                chars.next();
                let mut prev = '\0';
                for c2 in chars.by_ref() {
                    if prev == '*' && c2 == '/' {
                        break;
                    }
                    prev = c2;
                }
                out.push(' ');
            }
            '"' | '`' | '\'' => {
                skip_delimited(&mut chars, c);
                out.push(' ');
            }
            other => out.push(other),
        }
    }
    out
}

/// Consume characters up to and including the next unescaped `delim`.
fn skip_delimited<I: Iterator<Item = char>>(chars: &mut I, delim: char) {
    while let Some(c) = chars.next() {
        if c == '\\' {
            chars.next(); // skip the escaped character
            continue;
        }
        if c == delim {
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defines_main_is_token_aware() {
        assert!(defines_main("pub fn main() { 1 }"));
        assert!(defines_main("fn helper() {}\nfn main() { 0 }"));
        assert!(defines_main("async fn main() {}"));
        // The literal text in a string / comment must NOT count as a definition.
        assert!(!defines_main("let s = \"fn main\";"));
        assert!(!defines_main("// fn main\nlet x = 1;"));
        assert!(!defines_main("/* fn main */ let x = 1;"));
        assert!(!defines_main("let fn_main = 0;"));
        assert!(!defines_main("stratum::parse(\"a!(0)\")"));
    }

    #[test]
    fn ns_restore_guard_writes_back_on_unwind() {
        // A panic while the guard is live must still restore the caller's
        // namespace from the shared handle — never leave it wiped by `mem::take`.
        let mut ns = Namespace::new();
        ns.insert("keep", Obj::Bool(true));

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let shared: SharedNs = Arc::new(Mutex::new(std::mem::take(&mut ns)));
            let _restore = NsRestore {
                ns: &mut ns,
                shared: shared.clone(),
            };
            // Mutate through the shared handle, then unwind before any manual
            // write-back could run.
            shared.lock().unwrap().insert("added", Obj::Int(7));
            panic!("boom");
        }));

        assert!(result.is_err(), "the closure must have panicked");
        // The guard ran during unwinding: the original binding survived and the
        // mid-panic mutation was preserved.
        assert!(matches!(ns.get("keep"), Some(Obj::Bool(true))));
        assert!(matches!(ns.get("added"), Some(Obj::Int(7))));
    }
}
