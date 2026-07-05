//! Integration tests for the declaration preamble (`def`, `new`, macros) and
//! the `expand` transparency tool.
//!
//! Every construct is *pure surface sugar*: each positive case asserts the
//! sugared source desugars (structurally congruent, `≡`) to a hand-built core
//! term or to an equivalent raw source, and that `expand` output is transparent
//! (no `def`/`new`/macros) and re-parses faithfully.

use stratum_core::term::{drop_, input, lift, par, quote, zero, Name, Proc};
use stratum_core::{name_equiv, structurally_congruent};
use stratum_syntax::{expand, parse, to_source};

/// Assert `src` parses to a term structurally congruent to `expected`.
fn assert_parses(src: &str, expected: Proc) {
    let got = parse(src).unwrap_or_else(|e| panic!("`{src}` failed to parse: {e}"));
    assert!(
        structurally_congruent(&got, &expected),
        "`{src}` parsed to {got:?}, expected ≡ {expected:?}",
    );
}

/// Assert two sources parse to structurally congruent terms.
fn assert_same(a: &str, b: &str) {
    let pa = parse(a).unwrap_or_else(|e| panic!("`{a}` failed to parse: {e}"));
    let pb = parse(b).unwrap_or_else(|e| panic!("`{b}` failed to parse: {e}"));
    assert!(
        structurally_congruent(&pa, &pb),
        "`{a}` and `{b}` differ:\n  {pa:?}\n  {pb:?}",
    );
}

// --- `new`: ground-name generation -----------------------------------------

#[test]
fn new_mints_ground_names_in_order() {
    // `@0 = ground(0)` is reserved, so minting starts at ground(1):
    // req = ground(1) = @(@0!(0)), ack = ground(2) = @(@0!(@0!(0))).
    let req = quote(lift(quote(zero()), zero()));
    let ack = quote(lift(quote(zero()), lift(quote(zero()), zero())));
    let expected = par([
        lift(req.clone(), zero()),
        Proc::Input {
            chan: req,
            bound: 999, // α-equivalence ignores the symbol
            body: Box::new(lift(ack, zero())),
        },
    ]);
    assert_parses("new req, ack\nreq!(0) | req(x).ack!(0)", expected);
}

#[test]
fn new_equals_hand_written_raw() {
    assert_same(
        "new req, ack\nreq!(0) | req(x).ack!(0)",
        "@(@0!(0))!(0) | @(@0!(0))(x).@(@0!(@0!(0)))!(0)",
    );
}

// --- `def`: aliases ---------------------------------------------------------

#[test]
fn name_alias() {
    // def z { @0 }  z!(0)  ≡  @0!(0)
    assert_parses("def z { @0 }\nz!(0)", lift(quote(zero()), zero()));
    assert_same("def z { @0 }\nz!(0)", "@0!(0)");
}

#[test]
fn process_alias() {
    // def hello { @0!(0) }  hello | hello  ≡  @0!(0) | @0!(0)
    let one = lift(quote(zero()), zero());
    assert_parses(
        "def hello { @0!(0) }\nhello | hello",
        par([one.clone(), one]),
    );
}

#[test]
fn aliases_are_order_independent_and_nest() {
    // `a` references `b`, declared later.
    assert_same("def a { b }\ndef b { @0 }\na!(0)", "@0!(0)");
}

// --- macros -----------------------------------------------------------------

#[test]
fn macro_duplicates_argument() {
    // def par2(P) { P | P }  par2(@0!(0))  ≡  @0!(0) | @0!(0)
    let one = lift(quote(zero()), zero());
    assert_parses(
        "def par2(P) { P | P }\npar2(@0!(0))",
        par([one.clone(), one]),
    );
}

#[test]
fn macro_argument_in_name_position() {
    // A parameter used as a channel name.
    assert_same("def on(C) { C!(0) }\non(@0)", "@0!(0)");
}

#[test]
fn macro_captures_nothing_from_call_site() {
    // The argument `*y` refers to the call-site binder `y`, not anything in the
    // macro body.
    assert_same("def id(P) { P }\n@0(y).id(*y)", "@0(y).*y");
}

// --- named macro arguments --------------------------------------------------

#[test]
fn named_call_equals_positional_and_permuted() {
    // `def f(x, y) { x!(0) | y!(0) }`: positional, named, and permuted-named
    // calls all route the same arguments to the same holes.
    let def = "def f(x, y) { x!(0) | y!(0) }\n";
    let positional = format!("{def}f(@0, @(@0!(0)))");
    let named = format!("{def}f(x <- @0, y <- @(@0!(0)))");
    let permuted = format!("{def}f(y <- @(@0!(0)), x <- @0)");
    assert_same(&positional, &named);
    assert_same(&named, &permuted);
    // And all three equal the hand-written expansion.
    let expected = par([
        lift(quote(zero()), zero()),
        lift(quote(lift(quote(zero()), zero())), zero()),
    ]);
    assert_parses(&positional, expected);
}

#[test]
fn named_call_routes_mixed_sorts_when_swapped() {
    // `send` takes a name-param `C` and a process-param `P`; passing them by
    // name in swapped order still lands each in the right hole.
    assert_same(
        "def send(C, P) { C!(P) }\nsend(P <- @0!(0), C <- @0)",
        "@0!(@0!(0))",
    );
    // Same as positional `send(@0, @0!(0))`.
    assert_same(
        "def send(C, P) { C!(P) }\nsend(P <- @0!(0), C <- @0)",
        "def send(C, P) { C!(P) }\nsend(@0, @0!(0))",
    );
}

#[test]
fn named_call_still_sort_checks() {
    // Passing a process to the name-param `C` BY NAME still errors, exactly as
    // the positional call would.
    let e = parse("def send(C, P) { C!(P) }\nsend(C <- @0!(0), P <- @0)").unwrap_err();
    assert!(
        e.message.contains("name") && e.message.contains("process"),
        "got: {e}"
    );
}

#[test]
fn error_named_unknown_parameter() {
    let e = parse("def f(x, y) { x!(0) | y!(0) }\nf(z <- @0)").unwrap_err();
    assert!(e.message.contains("no parameter named `z`"), "got: {e}");
}

#[test]
fn error_named_duplicate_parameter() {
    let e = parse("def f(x, y) { x!(0) | y!(0) }\nf(x <- @0, x <- @0)").unwrap_err();
    assert!(
        e.message.contains("duplicate argument for parameter `x`"),
        "got: {e}"
    );
}

#[test]
fn error_named_missing_parameter() {
    let e = parse("def f(x, y) { x!(0) | y!(0) }\nf(x <- @0)").unwrap_err();
    assert!(
        e.message.contains("missing argument for parameter `y`"),
        "got: {e}"
    );
}

#[test]
fn error_mix_positional_then_named() {
    let e = parse("def f(x, y) { x!(0) | y!(0) }\nf(@0, y <- @0)").unwrap_err();
    assert!(
        e.message
            .contains("cannot mix positional and named arguments"),
        "got: {e}"
    );
}

#[test]
fn error_mix_named_then_positional() {
    let e = parse("def f(x, y) { x!(0) | y!(0) }\nf(x <- @0, @0)").unwrap_err();
    assert!(
        e.message
            .contains("cannot mix positional and named arguments"),
        "got: {e}"
    );
}

#[test]
fn named_call_expand_round_trips() {
    let src = "def f(x, y) { x!(0) | y!(0) }\nf(y <- @(@0!(0)), x <- @0)";
    let raw = expand(src).unwrap_or_else(|e| panic!("expand(`{src}`) failed: {e}"));
    assert!(
        !raw.contains("def") && !raw.contains("<-"),
        "raw still sugared: `{raw}`"
    );
    assert!(structurally_congruent(
        &parse(&raw).unwrap(),
        &parse(src).unwrap(),
    ));
}

// --- hygiene ----------------------------------------------------------------

#[test]
fn macro_local_new_is_fresh_per_expansion() {
    // Each expansion of `selfchan` mints a distinct internal channel `c`, so the
    // two top-level lifts fire on different channels.
    let p = parse("def selfchan(P) { new c c!(P) }\nselfchan(0) | selfchan(0)").unwrap();
    let chans: Vec<Name> = match &p {
        Proc::Par(items) => items
            .iter()
            .map(|it| match it {
                Proc::Lift { chan, .. } => chan.clone(),
                other => panic!("expected a lift, got {other:?}"),
            })
            .collect(),
        other => panic!("expected a parallel of two lifts, got {other:?}"),
    };
    assert_eq!(chans.len(), 2);
    assert!(
        !name_equiv(&chans[0], &chans[1]),
        "the two internal `c` channels must be distinct, got {:?} and {:?}",
        chans[0],
        chans[1],
    );
    assert!(p.is_closed());
}

// --- expand round-trip ------------------------------------------------------

#[test]
fn expand_is_transparent_and_faithful() {
    let sources = [
        "new req, ack\nreq!(0) | req(x).ack!(0)",
        "def z { @0 }\nz!(0)",
        "def hello { @0!(0) }\nhello | hello",
        "def par2(P) { P | P }\npar2(@0!(0))",
        "def selfchan(P) { new c c!(P) }\nselfchan(0) | selfchan(0)",
        "@0!(0) | @0(y).(*y | @0!(0))",
    ];
    for src in sources {
        let raw = expand(src).unwrap_or_else(|e| panic!("expand(`{src}`) failed: {e}"));
        // Transparent: no sugar survives.
        assert!(
            !raw.contains("def") && !raw.contains("new"),
            "expand(`{src}`) still contains sugar: `{raw}`",
        );
        // Faithful: re-parses to the same core term.
        let reparsed = parse(&raw).unwrap_or_else(|e| panic!("re-parse of `{raw}` failed: {e}"));
        let original = parse(src).unwrap();
        assert!(
            structurally_congruent(&reparsed, &original),
            "expand round-trip diverged for `{src}`: raw=`{raw}`",
        );
    }
}

#[test]
fn expand_sample_is_verbatim() {
    // The desugaring the reviewer eyeballs.
    assert_eq!(
        expand("new req, ack\nreq!(0) | req(x).ack!(0)").unwrap(),
        "@(@0!(0))!(0) | @(@0!(0))(v0).@(@0!(@0!(0)))!(0)",
    );
}

#[test]
fn to_source_round_trips() {
    let p = input(quote(zero()), |y| {
        par([drop_(y), lift(quote(zero()), zero())])
    });
    let src = to_source(&p);
    assert!(structurally_congruent(&parse(&src).unwrap(), &p));
}

// --- a worked encoding: the paper's replication ----------------------------

#[test]
fn bang_replication_encoding_parses_closed() {
    let src = "def bang(P) { new x  x!( x(y).( x!(*y) | *y ) | P ) | x(y).( x!(*y) | *y ) }\n\
               bang(@0!(0))";
    let p = parse(src).unwrap_or_else(|e| panic!("bang encoding failed to parse: {e}"));
    assert!(
        p.is_closed(),
        "the expansion of `bang(@0!(0))` must be closed"
    );
    // And it is transparently expandable to a re-parseable raw term.
    let raw = expand(src).unwrap();
    assert!(!raw.contains("def") && !raw.contains("new"));
    assert!(structurally_congruent(&parse(&raw).unwrap(), &p));
}

// --- error cases ------------------------------------------------------------

#[test]
fn error_unbound_identifier_in_program() {
    let e = parse("def z { @0 }\nw!(0)").unwrap_err();
    assert!(e.message.contains("unbound identifier `w`"), "got: {e}");
}

#[test]
fn error_wrong_macro_arity() {
    let e = parse("def par2(P) { P | P }\npar2(@0!(0), @0!(0))").unwrap_err();
    assert!(
        e.message.contains("expects 1 argument") && e.message.contains("got 2"),
        "got: {e}"
    );
}

#[test]
fn error_name_def_used_in_process_position() {
    // `z` is a name-def; using it bare as a process is a mismatch.
    let e = parse("def z { @0 }\nz").unwrap_err();
    assert!(
        e.message.contains("name") && e.message.contains("process"),
        "got: {e}"
    );
}

#[test]
fn error_process_def_used_in_name_position() {
    // `hello` is a process-def; using it as a channel name is a mismatch.
    let e = parse("def hello { @0!(0) }\nhello!(0)").unwrap_err();
    assert!(
        e.message.contains("process") && e.message.contains("name"),
        "got: {e}"
    );
}

#[test]
fn error_cyclic_definition() {
    let e = parse("def a { b }\ndef b { a }\na!(0)").unwrap_err();
    assert!(e.message.contains("cyclic"), "got: {e}");
}

#[test]
fn error_missing_program() {
    let e = parse("def z { @0 }").unwrap_err();
    assert!(e.message.contains("program"), "got: {e}");
    // A file of only declarations, and even an empty file, is rejected.
    assert!(parse("").is_err());
    assert!(parse("new a").is_err());
}

#[test]
fn error_duplicate_definition() {
    let e = parse("def z { @0 }\ndef z { @0!(0) }\nz!(0)").unwrap_err();
    assert!(e.message.contains("duplicate"), "got: {e}");
}
