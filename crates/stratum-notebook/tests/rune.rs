//! Integration tests for the `#rune` cell magic: scripting over the real
//! toolkit objects, sharing the session namespace across cells, faithfulness
//! against the equivalent directive, and clean handling of every failure mode
//! (compile error, runtime error, and a runaway loop hitting the budget).

use std::sync::mpsc;
use std::time::Duration;

use stratum_notebook::{evaluate, CellOutcome, Namespace, Obj};

/// A one-shot request/acknowledge protocol; after the communication nothing
/// emits on `req`, so `EF emits(ack)` holds and `AG emits(req)` fails.
const HANDSHAKE: &str = "new req, ack\n\nreq!(0) | req(x).ack!(0)";

/// Assert a cell produced no error, returning the outcome for further checks.
fn ok(out: CellOutcome) -> CellOutcome {
    assert!(
        out.error.is_none(),
        "unexpected cell error: {:?}",
        out.error
    );
    out
}

// ---------------------------------------------------------------------------
// Basic scripting: parse + explore + print.
// ---------------------------------------------------------------------------

#[test]
fn rune_parse_explore_and_print() {
    let mut ns = Namespace::new();
    let out = ok(evaluate(
        "#rune\n\
         let p = stratum::parse(\"new a\\na!(0)\");\n\
         let lts = stratum::explore(p, 100);\n\
         println!(\"states={}\", lts.num_states());\n",
        &mut ns,
    ));
    assert!(
        out.stream_stdout.contains("states="),
        "stdout was: {:?}",
        out.stream_stdout
    );
}

// ---------------------------------------------------------------------------
// Cross-cell namespace sharing: read a PRIOR DSL binding, compute a metric over
// ScLts states, write a result back, and read it in a LATER cell.
// ---------------------------------------------------------------------------

#[test]
fn rune_shares_namespace_across_cells() {
    let mut ns = Namespace::new();

    // Cell 1 (DSL): bind a process `mp`.
    ok(evaluate("#define mp\nnew a\n\na!(0) | a(x).0", &mut ns));
    assert!(matches!(ns.get("mp"), Some(Obj::Proc(_))));

    // Cell 2 (rune): read `mp`, explore it, count normal-form states, and write
    // the count back into the session.
    let out = ok(evaluate(
        "#rune\n\
         let p = stratum::get(\"mp\");\n\
         let lts = stratum::explore(p, 100);\n\
         let n = 0;\n\
         for i in 0..lts.num_states() {\n\
             if lts.state(i).is_normal_form() { n += 1; }\n\
         }\n\
         stratum::set(\"nf_count\", n);\n\
         println!(\"nf={}\", n);\n",
        &mut ns,
    ));
    assert!(out.stream_stdout.contains("nf="), "{:?}", out.stream_stdout);

    // The metric was written back as a first-class binding.
    let count = match ns.get("nf_count") {
        Some(Obj::Int(i)) => *i,
        other => panic!("expected an int binding, got {other:?}"),
    };
    assert!(count >= 1, "at least one state should be a normal form");

    // Cell 3 (rune): a LATER cell reads the value written by cell 2.
    let out = ok(evaluate(
        "#rune\n\
         let n = stratum::get(\"nf_count\");\n\
         println!(\"read {}\", n);\n",
        &mut ns,
    ));
    assert!(
        out.stream_stdout.contains(&format!("read {count}")),
        "stdout was: {:?}",
        out.stream_stdout
    );
}

// ---------------------------------------------------------------------------
// Faithfulness: `stratum::check` from a script agrees with the `#check`
// directive on the same LTS + formula.
// ---------------------------------------------------------------------------

#[test]
fn rune_check_agrees_with_directive() {
    for (formula, _label) in [("EF emits(ack)", "holds"), ("AG emits(req)", "fails")] {
        let mut ns = Namespace::new();
        ok(evaluate(HANDSHAKE, &mut ns));
        ok(evaluate("#explore _1 -> lts", &mut ns));

        // Directive verdict.
        let directive = ok(evaluate(&format!("#check {formula} on lts"), &mut ns));
        let directive_holds = directive.displays[0].text_plain.starts_with("Holds");

        // Scripted verdict against the same binding + formula.
        let scripted = ok(evaluate(
            &format!(
                "#rune\n\
                 let lts = stratum::get(\"lts\");\n\
                 println!(\"{{}}\", stratum::check(lts, \"{formula}\"));\n"
            ),
            &mut ns,
        ));
        let scripted_holds = scripted.stream_stdout.trim() == "true";

        assert_eq!(
            directive_holds, scripted_holds,
            "directive and script disagree on `{formula}`: \
             directive={directive_holds}, script={scripted_holds}"
        );
    }
}

// ---------------------------------------------------------------------------
// Return-value rendering: a script whose final expression is an ScLts yields an
// SVG display, just like the `#explore` directive.
// ---------------------------------------------------------------------------

#[test]
fn rune_return_value_renders_lts_listing() {
    let mut ns = Namespace::new();
    let out = ok(evaluate(
        "#rune\n\
         stratum::explore(stratum::parse(\"new a\\na!(0) | a(x).0\"), 100)\n",
        &mut ns,
    ));
    assert_eq!(out.displays.len(), 1, "expected one display");
    let bundle = &out.displays[0];
    assert!(
        bundle.text_plain.starts_with("LTS:"),
        "plain was: {:?}",
        bundle.text_plain
    );
    // A returned LTS renders as a plain listing (no diagram, ASCII by default).
    assert!(bundle.text_latex.is_none());
    assert!(bundle.text_plain.contains("s0"), "{:?}", bundle.text_plain);
}

#[test]
fn rune_return_verdict_renders_plain() {
    let mut ns = Namespace::new();
    let out = ok(evaluate(
        "#rune\n\
         let p = stratum::parse(\"new a\\na!(0)\");\n\
         stratum::bisim(p, p, false)\n",
        &mut ns,
    ));
    let bundle = &out.displays[0];
    assert!(
        bundle.text_plain.contains("Equivalent"),
        "{:?}",
        bundle.text_plain
    );
}

// ---------------------------------------------------------------------------
// Error paths — each a clean CellError, never a panic or hang.
// ---------------------------------------------------------------------------

#[test]
fn rune_compile_error_is_clean() {
    let mut ns = Namespace::new();
    let out = evaluate("#rune\n let x = ;\n", &mut ns);
    let err = out
        .error
        .expect("a syntax error must surface as a CellError");
    assert_eq!(err.ename, "RuneCompileError");
    assert!(!err.traceback.is_empty());
}

#[test]
fn rune_missing_name_is_clean_runtime_error() {
    let mut ns = Namespace::new();
    let out = evaluate(
        "#rune\n let x = stratum::get(\"does_not_exist\");\n",
        &mut ns,
    );
    let err = out
        .error
        .expect("a missing name must surface as a CellError");
    assert_eq!(err.ename, "RuneRuntimeError");
    assert!(
        err.evalue.contains("does_not_exist"),
        "evalue was: {}",
        err.evalue
    );
}

#[test]
fn rune_type_mismatch_is_clean_runtime_error() {
    let mut ns = Namespace::new();
    // Bind a *process* named `mp`, then misuse it as an LTS from a script.
    ok(evaluate("#define mp\nnew a\n\na!(0)", &mut ns));
    let out = evaluate(
        "#rune\n let p = stratum::get(\"mp\");\n let n = p.num_states();\n",
        &mut ns,
    );
    let err = out
        .error
        .expect("a type mismatch must surface as a CellError");
    assert_eq!(err.ename, "RuneRuntimeError");
}

#[test]
fn rune_runaway_loop_hits_budget_without_hanging() {
    // Run the runaway cell on a worker thread and require it to terminate well
    // within a timeout — the instruction budget must stop it, not a hang.
    let (tx, rx) = mpsc::channel();
    let handle = std::thread::spawn(move || {
        let mut ns = Namespace::new();
        let out = evaluate("#rune\n let i = 0;\n while true { i += 1; }\n", &mut ns);
        let _ = tx.send(out);
    });

    let out = rx
        .recv_timeout(Duration::from_secs(60))
        .expect("the runaway script must terminate via the budget, not hang the kernel");
    handle.join().unwrap();

    let err = out
        .error
        .expect("a runaway loop must surface as a CellError");
    assert_eq!(err.ename, "RuneBudgetError");
    assert!(err.evalue.contains("budget"), "evalue was: {}", err.evalue);
}
