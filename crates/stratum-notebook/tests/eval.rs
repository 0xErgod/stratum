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

    // A named DSL binding persists.
    let out = eval(
        "p = new a

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
    let out = eval("%explore p -> g", &mut ns);
    ok_display(&out);
    assert!(matches!(ns.get("g"), Some(Obj::Lts(_))));
}

// ---------------------------------------------------------------------------
// Renderers
// ---------------------------------------------------------------------------

#[test]
fn dsl_render_shows_transparency_pair() {
    let mut ns = Namespace::new();
    let out = eval(HANDSHAKE, &mut ns);
    let b = ok_display(&out);
    assert!(!b.text_plain.is_empty());
    let html = b.text_html.as_ref().expect("proc renders text/html");
    assert!(html.contains("surface"), "html: {html}");
    assert!(html.contains("core"), "html: {html}");
}

#[test]
fn lts_renders_valid_svg() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    let out = eval("%explore _1 -> lts", &mut ns);
    let b = ok_display(&out);
    let svg = b.image_svg.as_ref().expect("LTS renders image/svg+xml");
    assert!(
        svg.contains("<svg"),
        "not an svg: {}",
        &svg[..svg.len().min(80)]
    );
    assert!(svg.len() > 100, "svg suspiciously short");
    assert!(b.text_plain.contains("states"));
    assert!(b.text_plain.contains("transitions"));
}

#[test]
fn verdict_renders_html() {
    let mut ns = Namespace::new();
    eval(
        "p = new a

a!(0)",
        &mut ns,
    );
    eval(
        "q = new a

a!(0)",
        &mut ns,
    );
    let out = eval("%bisim p q", &mut ns);
    let b = ok_display(&out);
    let html = b.text_html.as_ref().expect("verdict renders html");
    assert!(
        html.contains("Equivalent")
            || html.contains("Distinguished")
            || html.contains("Inconclusive"),
        "html: {html}"
    );
}

#[test]
fn trace_renders_step_table() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("%explore _1 -> lts", &mut ns);
    let out = eval("%trace lts", &mut ns);
    let b = ok_display(&out);
    let html = b.text_html.as_ref().expect("trace renders html table");
    assert!(html.contains("<table"), "html: {html}");
    assert!(html.contains("channel"));
    assert!(b.text_plain.contains("step"));
}

#[test]
fn expand_shows_core() {
    let mut ns = Namespace::new();
    // Inline expand of surface DSL.
    let out = eval(
        "%expand new a

a!(0)",
        &mut ns,
    );
    let b = ok_display(&out);
    assert!(!b.text_plain.is_empty());
    // Named expand of a bound proc.
    eval(
        "p = new a

a!(0)",
        &mut ns,
    );
    let out = eval("%expand p", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_html.as_ref().unwrap().contains("core"));
}

// ---------------------------------------------------------------------------
// Formula sub-language (via %check and directly)
// ---------------------------------------------------------------------------

#[test]
fn formula_fragment_parses_and_checks() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("%explore _1 -> lts", &mut ns);

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
        let out = eval(&format!("%check {f} on lts"), &mut ns);
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
    eval("%explore _1 -> lts", &mut ns);

    // Missing operand.
    let out = eval("%check EF & emits(ack) on lts", &mut ns);
    let err = out.error.expect("malformed formula must error");
    assert_eq!(err.ename, "FormulaError");

    // Unknown channel in emits(...).
    let out = eval("%check EF emits(nope) on lts", &mut ns);
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
        "%step new a

a!(0) | a(x).0",
        &mut ns,
    );
    let b = ok_display(&out);
    assert!(b.text_plain.contains("reduct"), "plain: {}", b.text_plain);
    assert!(b.text_html.as_ref().unwrap().contains("<table"));
}

#[test]
fn typecheck_ok_and_error() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);

    // Well-typed: both channels carry Nil.
    let out = eval("%typecheck _1 with req:Nil, ack:Nil", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.contains("well-typed"),
        "plain: {}",
        b.text_plain
    );

    // Default empty environment still checks (unsorted channel is an error we
    // surface via the renderer, not a cell error).
    let out = eval("%typecheck _1", &mut ns);
    ok_display(&out);
}

#[test]
fn witness_and_counterexample() {
    let mut ns = Namespace::new();
    eval(HANDSHAKE, &mut ns);
    eval("%explore _1 -> lts", &mut ns);

    let out = eval("%witness EF emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(b.text_html.as_ref().unwrap().contains("witness"));

    let out = eval("%counterexample AG emits(req) on lts", &mut ns);
    let b = ok_display(&out);
    // AG emits(req) is false (after the comm nothing emits on req), so there is
    // a counterexample run.
    assert!(b.text_html.as_ref().unwrap().contains("counterexample"));
}

#[test]
fn unknown_directive_errors() {
    let mut ns = Namespace::new();
    let out = eval("%frobnicate lts", &mut ns);
    let err = out.error.expect("unknown directive must error");
    assert_eq!(err.ename, "DirectiveError");
    assert!(err.evalue.contains("frobnicate"));
}

#[test]
fn bad_arity_errors() {
    let mut ns = Namespace::new();
    let out = eval("%explore", &mut ns);
    let err = out.error.expect("empty explore must error");
    assert_eq!(err.ename, "DirectiveError");

    let out = eval("%check EF emits(ack)", &mut ns);
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
fn reserved_and_unknown_magics_error() {
    let mut ns = Namespace::new();
    let out = eval("%%rune\nsome code", &mut ns);
    let err = out.error.expect("%%rune reserved");
    assert_eq!(err.ename, "MagicError");
    assert!(err.evalue.contains("rune"));

    let out = eval("%%bogus", &mut ns);
    let err = out.error.expect("unknown magic");
    assert_eq!(err.ename, "MagicError");
}

#[test]
fn help_lists_directives() {
    let mut ns = Namespace::new();
    let out = eval("%help", &mut ns);
    let b = ok_display(&out);
    for d in ["%explore", "%check", "%bisim", "%typecheck", "emits("] {
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
    let out = eval("%explore _1 -> lts", &mut ns);
    ok_display(&out);

    // EF emits(ack): the request can be acknowledged — true.
    let out = eval("%check EF emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.starts_with("Holds"),
        "EF emits(ack) should hold: {}",
        b.text_plain
    );

    // AG emits(ack): it is always acknowledged — false (the initial state does
    // not emit on ack).
    let out = eval("%check AG emits(ack) on lts", &mut ns);
    let b = ok_display(&out);
    assert!(
        b.text_plain.starts_with("Does not hold"),
        "AG emits(ack) should not hold: {}",
        b.text_plain
    );
}
