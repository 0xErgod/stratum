//! Integration tests for the notebook evaluator: namespace persistence, every
//! renderer, the formula sub-language, each directive (happy + error path), and
//! the request/acknowledge handshake end to end.

use stratum_notebook::{evaluate, CellOutcome, Namespace, Obj};

/// The one-shot request/acknowledge handshake in the surface syntax.
const HANDSHAKE: &str = "new req, ack\n\nreq!(0) | req(x).ack!(0)";

fn eval(cell: &str, ns: &mut Namespace) -> CellOutcome {
    evaluate(cell, ns)
}

/// Assert the cell produced no error and return its first display's bundle.
fn ok_display(out: &CellOutcome) -> &stratum_notebook::MimeBundle {
    assert!(
        out.error.is_none(),
        "unexpected cell error: {:?}",
        out.error
    );
    assert!(!out.displays.is_empty(), "expected at least one display");
    &out.displays[0]
}

// ---------------------------------------------------------------------------
// Namespace persistence
// ---------------------------------------------------------------------------

#[test]
fn namespace_binds_and_looks_up_across_cells() {
    let mut ns = Namespace::new();

    // A `#define` binding persists.
    let out = eval(
        "#define p
new a

a!(0)",
        &mut ns,
    );
    ok_display(&out);
    assert!(matches!(ns.get("p"), Some(Obj::Proc(_))));

    // An unnamed DSL cell gets an auto name and does not clobber `p`.
    let out = eval(
        "new b

b!(0)",
        &mut ns,
    );
    ok_display(&out);
    assert!(matches!(ns.get("p"), Some(Obj::Proc(_))));
    assert!(matches!(ns.get("_1"), Some(Obj::Proc(_))));

    // A directive can consume a name bound in an earlier cell.
    let out = eval("#explore p -> g", &mut ns);
    ok_display(&out);
    assert!(matches!(ns.get("g"), Some(Obj::Lts { .. })));
}

#[test]
fn define_inline_and_header_forms() {
    let mut ns = Namespace::new();

    // Inline form: `#define <name> <expr>` on one line.
    let out = eval("#define emitter @0!(0)", &mut ns);
    ok_display(&out);
    assert!(matches!(ns.get("emitter"), Some(Obj::Proc(_))));

    // Header form: `#define <name>` then the Stratum code below.
    let out = eval("#define quiet\n@0(x).0", &mut ns);
    ok_display(&out);
    assert!(matches!(ns.get("quiet"), Some(Obj::Proc(_))));

    // A `#define` with no body is a clear error, not a parse crash.
    let out = eval("#define lonely", &mut ns);
    let err = out.error.expect("empty define must error");
    assert_eq!(err.ename, "DefineError");
}

// ---------------------------------------------------------------------------
// Renderers
// ---------------------------------------------------------------------------

#[test]
fn dsl_render_shows_surface_only() {
    let mut ns = Namespace::new();
    let out = eval(HANDSHAKE, &mut ns);
    let b = ok_display(&out);
    // Surface form only — the folded channel names, no desugared core.
    assert_eq!(b.text_plain, "req!(0) | req(v0).ack!(0)");
    // ASCII mode (the default) emits no LaTeX.
    assert!(b.text_latex.is_none());
}

#[test]
fn lts_renders_as_listing() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    let out = eval("#explore _1 -> lts", &mut ns);
    let b = ok_display(&out);
    // No diagram — a plain-text states + transitions listing.
    assert!(b.text_latex.is_none());
    assert!(b.text_plain.contains("states"));
    assert!(b.text_plain.contains("transitions"));
    assert!(b.text_plain.contains("s0"), "listing: {}", b.text_plain);
    assert!(b.text_plain.contains("-->"), "listing: {}", b.text_plain);
}

#[test]
fn verdict_renders_plain() {
    let mut ns = Namespace::new();
    eval(
        "#define p
new a

a!(0)",
        &mut ns,
    );
    eval(
        "#define q
new a

a!(0)",
        &mut ns,
    );
    let out = eval("#bisim p q", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.contains("Equivalent")
            || b.text_plain.contains("Distinguished")
            || b.text_plain.contains("Inconclusive"),
        "plain: {}",
        b.text_plain
    );
}

#[test]
fn trace_renders_step_listing() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("#explore _1 -> lts", &mut ns);
    let out = eval("#trace lts", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains("step"));
    assert!(b.text_plain.contains("-->"), "trace: {}", b.text_plain);
}

#[test]
fn expand_shows_core() {
    let mut ns = Namespace::new();
    // Inline expand of surface DSL desugars to the raw core (explicit quotes).
    let out = eval(
        "#expand new a

a!(0)",
        &mut ns,
    );
    let b = ok_display(&out);
    assert!(b.text_plain.contains('@'), "core: {}", b.text_plain);
    // Named expand of a bound proc.
    eval(
        "#define p
new a

a!(0)",
        &mut ns,
    );
    let out = eval("#expand p", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains('@'), "core: {}", b.text_plain);
}

// ---------------------------------------------------------------------------
// Formula sub-language (via #check and directly)
// ---------------------------------------------------------------------------

#[test]
fn formula_fragment_parses_and_checks() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("#explore _1 -> lts", &mut ns);

    // Every modality + connective + emits atom, on a real LTS.
    for f in [
        "EF emits(ack)",
        "AG emits(req) | EF emits(ack)",
        "!AG emits(ack)",
        "EF (emits(ack) & !emits(req))",
        "AF emits(ack)",
        "EG emits(req)",
        "EX emits(ack)",
    ] {
        let out = eval(&format!("#check {f} on lts"), &mut ns);
        assert!(
            out.error.is_none(),
            "formula `{f}` errored: {:?}",
            out.error
        );
    }
}

#[test]
fn malformed_formula_is_a_clear_error() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("#explore _1 -> lts", &mut ns);

    // Missing operand.
    let out = eval("#check EF & emits(ack) on lts", &mut ns);
    let err = out.error.expect("malformed formula must error");
    assert_eq!(err.ename, "FormulaError");

    // Unknown channel in emits(...).
    let out = eval("#check EF emits(nope) on lts", &mut ns);
    let err = out.error.expect("unknown channel must error");
    assert_eq!(err.ename, "FormulaError");
    assert!(err.evalue.contains("nope"), "evalue: {}", err.evalue);
}

// ---------------------------------------------------------------------------
// Directives: happy path + error path
// ---------------------------------------------------------------------------

#[test]
fn step_shows_reducts() {
    let mut ns = Namespace::new();
    let out = eval(
        "#step new a

a!(0) | a(x).0",
        &mut ns,
    );
    let b = ok_display(&out);
    assert!(b.text_plain.contains("reduct"), "plain: {}", b.text_plain);
}

#[test]
fn typecheck_ok_and_error() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);

    // Well-typed: both channels carry Nil.
    let out = eval("#typecheck _1 with req:Nil, ack:Nil", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.contains("well-typed"),
        "plain: {}",
        b.text_plain
    );

    // Default empty environment still checks (unsorted channel is an error we
    // surface via the renderer, not a cell error).
    let out = eval("#typecheck _1", &mut ns);
    ok_display(&out);
}

#[test]
fn witness_and_counterexample() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("#explore _1 -> lts", &mut ns);

    let out = eval("#witness EF emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains("witness"), "plain: {}", b.text_plain);

    let out = eval("#counterexample AG emits(req) on lts", &mut ns);
    let b = ok_display(&out);
    // AG emits(req) is false (after the comm nothing emits on req), so there is
    // a counterexample run.
    assert!(
        b.text_plain.contains("counterexample"),
        "plain: {}",
        b.text_plain
    );
}

#[test]
fn unknown_directive_errors() {
    let mut ns = Namespace::new();
    let out = eval("#frobnicate lts", &mut ns);
    let err = out.error.expect("unknown directive must error");
    assert_eq!(err.ename, "DirectiveError");
    assert!(err.evalue.contains("frobnicate"));
}

#[test]
fn bad_arity_errors() {
    let mut ns = Namespace::new();
    let out = eval("#explore", &mut ns);
    let err = out.error.expect("empty explore must error");
    assert_eq!(err.ename, "DirectiveError");

    let out = eval("#check EF emits(ack)", &mut ns);
    let err = out.error.expect("check without `on` must error");
    assert_eq!(err.ename, "DirectiveError");
}

#[test]
fn parse_error_has_span() {
    let mut ns = Namespace::new();
    let out = eval("new a in a!(", &mut ns);
    let err = out.error.expect("truncated DSL must error");
    assert_eq!(err.ename, "ParseError");
    // The traceback carries a caret line pointing into the source.
    assert!(
        err.traceback.iter().any(|l| l.contains('^')),
        "traceback: {:?}",
        err.traceback
    );
    assert!(err.evalue.contains("line"), "evalue: {}", err.evalue);
}

#[test]
fn help_lists_directives() {
    let mut ns = Namespace::new();
    let out = eval("#help", &mut ns);
    let b = ok_display(&out);
    for d in ["#explore", "#check", "#bisim", "#typecheck", "emits("] {
        assert!(b.text_plain.contains(d), "help missing {d}");
    }
}

// ---------------------------------------------------------------------------
// The handshake, end to end
// ---------------------------------------------------------------------------

#[test]
fn handshake_end_to_end() {
    let mut ns = Namespace::new();

    // Define the protocol.
    let out = eval(HANDSHAKE, &mut ns);
    ok_display(&out);

    // Explore its trace LTS and bind it.
    let out = eval("#explore _1 -> lts", &mut ns);
    ok_display(&out);

    // EF emits(ack): the request can be acknowledged — true.
    let out = eval("#check EF emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.starts_with("Holds"),
        "EF emits(ack) should hold: {}",
        b.text_plain
    );

    // AG emits(ack): it is always acknowledged — false (the initial state does
    // not emit on ack).
    let out = eval("#check AG emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.starts_with("Does not hold"),
        "AG emits(ack) should not hold: {}",
        b.text_plain
    );
}

// ---------------------------------------------------------------------------
// Depth guards: pathologically nested input must produce a clean error, not a
// stack overflow that aborts the process.
// ---------------------------------------------------------------------------

#[test]
fn deeply_nested_formula_errors_cleanly() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("#explore _1 -> lts", &mut ns);

    // ~400 nested EF(...) — well past the parser's depth cap.
    let formula = format!("EF {}emits(ack){}", "(".repeat(400), ")".repeat(400));
    let out = eval(&format!("#check {formula} on lts"), &mut ns);
    let err = out
        .error
        .expect("deeply-nested formula must error, not crash");
    assert_eq!(err.ename, "FormulaError");
    assert!(err.evalue.contains("deep"), "evalue: {}", err.evalue);
}

#[test]
fn deeply_nested_dsl_errors_cleanly() {
    let mut ns = Namespace::new();
    // ~600 nested parens: rejected by the pre-parse nesting guard before it can
    // overflow the (un-guarded) toolkit parser.
    let out = eval(&"(".repeat(600), &mut ns);
    let err = out.error.expect("deeply-nested DSL must error, not crash");
    assert_eq!(err.ename, "NestingError");

    // The same guard protects a directive that parses inline DSL.
    let out = eval(&format!("#step {}", "(".repeat(600)), &mut ns);
    let err = out.error.expect("deeply-nested inline DSL must error");
    assert_eq!(err.ename, "NestingError");
}

#[test]
fn deeply_nested_type_errors_cleanly() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    // ~600 nested Chan(...) in the typing environment.
    let ty = format!("req:{}Nil{}", "Chan(".repeat(600), ")".repeat(600));
    let out = eval(&format!("#typecheck _1 with {ty}"), &mut ns);
    let err = out.error.expect("deeply-nested type must error, not crash");
    assert_eq!(err.ename, "NestingError");
}

// ---------------------------------------------------------------------------
// Reduced-LTS soundness: EX rejection + verdict caveat.
// ---------------------------------------------------------------------------

#[test]
fn reduced_lts_rejects_ex_and_caveats_others() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    // A partial-order-reduced LTS.
    let out = eval("#explore _1 por -> rlts", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.contains("caveat"),
        "reduced explore should carry a caveat: {}",
        b.text_plain
    );

    // EX (next-time) is not preserved under reduction — must be rejected.
    let out = eval("#check EX emits(ack) on rlts", &mut ns);
    let err = out.error.expect("EX on a reduced LTS must be rejected");
    assert_eq!(err.ename, "ReductionError");
    assert!(err.evalue.contains("EX"), "evalue: {}", err.evalue);

    // A non-EX property is allowed but its rendering carries the caveat.
    let out = eval("#check EF emits(ack) on rlts", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.starts_with("Holds"), "plain: {}", b.text_plain);
    assert!(
        b.text_plain.contains("caveat"),
        "reduced verdict must carry a caveat: {}",
        b.text_plain
    );

    // Symmetry reduction behaves the same way for EX.
    let out = eval("#explore _1 sym=req,ack -> slts", &mut ns);
    ok_display(&out);
    let out = eval("#check EX emits(ack) on slts", &mut ns);
    assert_eq!(
        out.error.expect("EX on symmetry LTS").ename,
        "ReductionError"
    );

    // A full LTS has no caveat and accepts EX.
    eval("#explore _1 -> flts", &mut ns);
    let out = eval("#check EX emits(ack) on flts", &mut ns);
    let b = ok_display(&out);
    assert!(!b.text_plain.contains("caveat"), "full LTS must not caveat");
}

// ---------------------------------------------------------------------------
// Minor fixes: auto-name collision + bisim arity.
// ---------------------------------------------------------------------------

#[test]
fn auto_names_skip_user_bindings() {
    let mut ns = Namespace::new();
    // User explicitly claims `_1`.
    eval("#define _1\nnew a\n\na!(0)", &mut ns);
    // An unnamed cell must NOT clobber it — it should land on `_2`.
    eval("new b\n\nb!(0)", &mut ns);
    assert!(matches!(ns.get("_1"), Some(Obj::Proc(_))));
    assert!(matches!(ns.get("_2"), Some(Obj::Proc(_))));
}

#[test]
fn bisim_extra_args_error() {
    let mut ns = Namespace::new();
    eval("#define p\nnew a\n\na!(0)", &mut ns);
    let out = eval("#bisim p p p", &mut ns);
    let err = out.error.expect("extra bisim args must error");
    assert_eq!(err.ename, "DirectiveError");
}

// ---------------------------------------------------------------------------
// Representation modes: #ascii (default), #latex, #repr.
// ---------------------------------------------------------------------------

#[test]
fn latex_mode_emits_text_latex() {
    let mut ns = Namespace::new();

    // The default is ASCII: no LaTeX on a proc cell.
    let out = eval(HANDSHAKE, &mut ns);
    assert!(ok_display(&out).text_latex.is_none());

    // Switch to LaTeX; #latex reports the new mode.
    let out = eval("#latex", &mut ns);
    assert!(ok_display(&out).text_plain.contains("LaTeX"));

    // A proc now carries a classic-rho text/latex payload alongside the ASCII.
    let out = eval(
        "#define hs\nnew req, ack\n\nreq!(0) | req(x).ack!(0)",
        &mut ns,
    );
    let b = ok_display(&out);
    assert_eq!(b.text_plain, "req!(0) | req(v0).ack!(0)");
    let latex = b.text_latex.as_ref().expect("latex mode emits text/latex");
    // Meredith–Radestock lift brackets `x⟨|P|⟩`, not pi-calculus `\overline{x}`.
    assert!(latex.contains(r"\mathit{req}\langle\!|"), "latex: {latex}");
    assert!(latex.contains(r"\mid"), "latex: {latex}");

    // An LTS listing gets a LaTeX array with \xrightarrow edges.
    let out = eval("#explore hs -> g", &mut ns);
    let latex = ok_display(&out)
        .text_latex
        .as_ref()
        .expect("latex LTS listing")
        .clone();
    assert!(latex.contains(r"\begin{array}"), "latex: {latex}");
    assert!(latex.contains(r"\xrightarrow"), "latex: {latex}");

    // Back to ASCII: no more LaTeX.
    let out = eval("#ascii", &mut ns);
    assert!(ok_display(&out).text_plain.contains("ASCII"));
    let out = eval("#explore hs", &mut ns);
    assert!(ok_display(&out).text_latex.is_none());
}

#[test]
fn repr_reports_current_mode() {
    let mut ns = Namespace::new();
    // `#repr` alone does not change the mode; it reports the default.
    let out = eval("#repr", &mut ns);
    assert!(ok_display(&out).text_plain.contains("ASCII"));
    eval("#latex", &mut ns);
    let out = eval("#repr", &mut ns);
    assert!(ok_display(&out).text_plain.contains("LaTeX"));
}

// ---------------------------------------------------------------------------
// #traces / tr[i] / #trace / #lin / #project
// ---------------------------------------------------------------------------

/// A diamond (two independent reactions) is one trace; a race is two.
#[test]
fn traces_binds_and_lists() {
    let mut ns = Namespace::new();
    let out = eval(
        "#traces new a, b\na!(0) | a(x).0 | b!(0) | b(y).0 -> tr",
        &mut ns,
    );
    let b = ok_display(&out);
    assert!(
        b.text_plain.contains("Traces: 1 traces"),
        "{}",
        b.text_plain
    );
    assert!(b.text_plain.contains("tr[0]"), "{}", b.text_plain);
    // The binding is a trace-set.
    assert!(matches!(ns.get("tr"), Some(Obj::Traces { .. })));
}

#[test]
fn trace_handle_selects_and_renders() {
    let mut ns = Namespace::new();
    eval(
        "#traces new a, b\na!(0) | a(x).0 | b!(0) | b(y).0 -> tr",
        &mut ns,
    );
    // `#trace tr[0]` shows the partial order; the diamond is a parallel form.
    let out = eval("#trace tr[0]", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains("Trace: 2 events"), "{}", b.text_plain);
    assert!(b.text_plain.contains(" ∥ "), "{}", b.text_plain);
}

#[test]
fn lin_lists_linearizations() {
    let mut ns = Namespace::new();
    eval(
        "#traces new a, b\na!(0) | a(x).0 | b!(0) | b(y).0 -> tr",
        &mut ns,
    );
    // Two concurrent events -> two linearizations.
    let out = eval("#lin tr[0]", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains("2 linearization"), "{}", b.text_plain);
}

#[test]
fn project_restricts_to_an_agent() {
    let mut ns = Namespace::new();
    eval(
        "#traces new a, b\na!(0) | a(x).0 | b!(0) | b(y).0 -> tr",
        &mut ns,
    );
    // Projecting onto `a` keeps a single event.
    let out = eval("#project tr[0] a", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_plain.contains("Trace: 1 events"), "{}", b.text_plain);
}

#[test]
fn trace_handle_errors_are_clean() {
    let mut ns = Namespace::new();
    eval("#traces new a\na!(0) | a(x).0 -> tr", &mut ns);
    // Out-of-range index.
    let out = eval("#trace tr[9]", &mut ns);
    assert!(out.error.is_some(), "expected an index error");
    // Unknown trace-set.
    let out = eval("#lin nope[0]", &mut ns);
    assert!(out.error.is_some(), "expected a name error");
}
