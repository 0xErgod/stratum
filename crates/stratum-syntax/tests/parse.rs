//! Integration tests for the recursive-descent surface-syntax parser.
//!
//! Each positive case asserts that the parsed term is structurally congruent
//! (`≡`, up to α-equivalence and the parallel monoid) to the expected term built
//! with the `stratum-core` constructors.

use stratum_core::structurally_congruent;
use stratum_core::term::{drop_, input, lift, par, quote, zero, Proc};
use stratum_syntax::{parse, parse_name};

/// Assert `src` parses to a term structurally congruent to `expected`.
fn assert_parses(src: &str, expected: Proc) {
    let got = parse(src).unwrap_or_else(|e| panic!("`{src}` failed to parse: {e}"));
    assert!(
        structurally_congruent(&got, &expected),
        "`{src}` parsed to {got:?}, expected ≡ {expected:?}",
    );
}

#[test]
fn nil_zero() {
    assert_parses("0", zero());
}

#[test]
fn nil_keyword() {
    assert_parses("nil", zero());
}

#[test]
fn lift_quote_zero() {
    // @0!(0) → lift(quote(zero()), zero())
    assert_parses("@0!(0)", lift(quote(zero()), zero()));
}

#[test]
fn drop_quote_zero() {
    // *@0 → drop_(quote(zero()))
    assert_parses("*@0", drop_(quote(zero())));
}

#[test]
fn input_binds_and_drops() {
    // @0(y).*y → input(quote(zero()), |y| drop_(y))
    assert_parses("@0(y).*y", input(quote(zero()), drop_));
}

#[test]
fn parallel_of_two() {
    // @0!(0) | @0(y).*y
    let expected = par([lift(quote(zero()), zero()), input(quote(zero()), drop_)]);
    assert_parses("@0!(0) | @0(y).*y", expected);
}

#[test]
fn nested_grouped_continuation() {
    // @0(y).(*y | @0!(0))
    let expected = input(quote(zero()), |y| {
        par([drop_(y), lift(quote(zero()), zero())])
    });
    assert_parses("@0(y).(*y | @0!(0))", expected);
}

#[test]
fn quote_binds_tightly_over_lift() {
    // @0!(0) is (@0)!(0), NOT @(0!(0)); the arg is the null process.
    assert_parses("@0!(0)", lift(quote(zero()), zero()));
    // A quote of a lift needs explicit grouping.
    assert_parses(
        "@(@0!(0))!(0)",
        lift(quote(lift(quote(zero()), zero())), zero()),
    );
}

#[test]
fn shadowing_inner_binder_wins() {
    // Outer y is shadowed by the inner y; *y refers to the inner binder, whose
    // channel is @0. Compare against an α-renamed witness.
    let src = "@0(y).@0(z).@0(y).*y";
    let expected = input(quote(zero()), |_outer| {
        input(quote(zero()), |_mid| input(quote(zero()), drop_))
    });
    assert_parses(src, expected);
}

#[test]
fn whitespace_and_comments_ignored() {
    let src = "@0!(0)  // a lift\n  |  // then parallel\n  @0(y).*y\n";
    let expected = par([lift(quote(zero()), zero()), input(quote(zero()), drop_)]);
    assert_parses(src, expected);
}

#[test]
fn parallel_is_flat_and_associative() {
    // Grouping should not matter up to ≡.
    let a = parse("@0!(0) | @0!(0) | @0!(0)").unwrap();
    let b = parse("(@0!(0) | @0!(0)) | @0!(0)").unwrap();
    let c = parse("@0!(0) | (@0!(0) | @0!(0))").unwrap();
    assert!(structurally_congruent(&a, &b));
    assert!(structurally_congruent(&a, &c));
}

#[test]
fn quote_of_drop_name() {
    // @*@0 → quote(drop(quote(zero))); note quote-drop makes this ≡N @0 at the
    // name level, but as a process form it is a lift channel here.
    assert_parses("@*@0!(0)", lift(quote(drop_(quote(zero()))), zero()));
}

#[test]
fn parse_name_quote() {
    use stratum_core::name_equiv;
    let n = parse_name("@0").unwrap();
    assert!(name_equiv(&n, &quote(zero())));
}

// --- Error cases -----------------------------------------------------------

#[test]
fn error_unbound_identifier() {
    let e = parse("*y").unwrap_err();
    assert!(
        e.message.contains("unbound identifier `y`"),
        "unexpected message: {e}"
    );
}

#[test]
fn error_unbound_channel() {
    // `x` is free here — inputs bind their argument, not their channel.
    let e = parse("x!(0)").unwrap_err();
    assert!(e.message.contains("unbound identifier `x`"), "got: {e}");
}

#[test]
fn error_unclosed_paren() {
    let e = parse("(@0!(0)").unwrap_err();
    assert!(e.message.contains("`)`"), "got: {e}");
}

#[test]
fn error_bare_name_is_not_a_process() {
    // A name alone is not a process; it must be followed by `!` or `(`.
    let e = parse("@0").unwrap_err();
    assert!(
        e.message.contains("`!`") || e.message.contains("`(`"),
        "got: {e}"
    );
}

#[test]
fn error_lift_needs_process_arg() {
    let e = parse("@0!()").unwrap_err();
    assert!(e.message.contains("expected a process"), "got: {e}");
}

#[test]
fn error_input_binder_must_be_identifier() {
    let e = parse("@0(@0).*@0").unwrap_err();
    assert!(e.message.contains("identifier"), "got: {e}");
}

#[test]
fn error_trailing_garbage() {
    let e = parse("0 0").unwrap_err();
    assert!(e.message.contains("end of input"), "got: {e}");
}

#[test]
fn error_reports_position() {
    // The `y` is on line 2, column 2 (after a leading space).
    let e = parse("@0!(0)\n *y").unwrap_err();
    assert_eq!(e.line, 2);
    assert_eq!(e.column, 2);
}

#[test]
fn all_examples_are_closed() {
    // Every well-formed example must be a genuine (closed) term of the calculus.
    for src in [
        "0",
        "@0!(0)",
        "*@0",
        "@0(y).*y",
        "@0!(0) | @0(y).*y",
        "@0(y).(*y | @0!(0))",
    ] {
        let p = parse(src).unwrap();
        assert!(p.is_closed(), "`{src}` is not closed");
    }
}

// --- recursion-depth guard (issue #43) ---------------------------------------
//
// The recursive-descent parser must never overflow the process stack on
// deeply-nested input: a stack overflow is an *uncatchable* abort
// (`STATUS_STACK_OVERFLOW` / SIGSEGV) that would tear down the whole process
// (and, here, the test binary). Each test below feeds nesting far beyond any
// sane program and asserts a clean `Err(ParseError)` comes back. The proof that
// no overflow occurred is simply that the test binary survives to make the
// assertion — had the parser recursed unboundedly, the process would have
// aborted instead of returning.

/// Deeply-nested parenthesized groups return a clean error, not a crash.
#[test]
fn deeply_nested_parens_error_not_crash() {
    let src = format!("{}0{}", "(".repeat(5000), ")".repeat(5000));
    let err = parse(&src).expect_err("deeply-nested parens must be rejected, not overflow");
    assert!(
        err.message.contains("nested too deeply"),
        "expected a nesting-depth error, got: {err}",
    );
}

/// Deeply-nested quotes `@(@(@(…)))` return a clean error, not a crash.
#[test]
fn deeply_nested_quotes_error_not_crash() {
    // `@(*@(*@(… *@0 …)))`: each `@( *` layer nests a quote around a drop of the
    // next quote, driving the name/primary recursion arbitrarily deep.
    let n = 5000;
    let src = format!("*{}@0{}", "@(*".repeat(n), ")".repeat(n));
    let err = parse(&src).expect_err("deeply-nested quotes must be rejected, not overflow");
    assert!(
        err.message.contains("nested too deeply"),
        "expected a nesting-depth error, got: {err}",
    );
}

/// Deeply-nested lift bodies `x!(x!(… ))` return a clean error, not a crash.
#[test]
fn deeply_nested_lifts_error_not_crash() {
    let n = 5000;
    let src = format!("{}0{}", "@0!(".repeat(n), ")".repeat(n));
    let err = parse(&src).expect_err("deeply-nested lifts must be rejected, not overflow");
    assert!(
        err.message.contains("nested too deeply"),
        "expected a nesting-depth error, got: {err}",
    );
}

/// The depth error carries a meaningful (non-zero) source position.
#[test]
fn depth_error_has_position() {
    let src = format!("{}0{}", "(".repeat(5000), ")".repeat(5000));
    let err = parse(&src).unwrap_err();
    assert!(
        err.line >= 1 && err.column >= 1,
        "position should be set: {err}"
    );
}

/// A moderately-nested program (well within the cap) still parses fine: the
/// guard must not reject any reasonable input.
#[test]
fn moderate_nesting_still_parses() {
    // 20 levels of grouping around a lift — far deeper than any real protocol,
    // yet comfortably under the depth cap.
    let src = format!("{}@0!(0){}", "(".repeat(20), ")".repeat(20));
    let p = parse(&src).unwrap_or_else(|e| panic!("20-deep nesting should parse: {e}"));
    assert!(p.is_closed());

    // A 20-deep nest of quotes (as a drop, a valid process) likewise parses.
    let src = format!("*{}@0{}", "@(*".repeat(20), ")".repeat(20));
    parse(&src).unwrap_or_else(|e| panic!("20-deep quotes should parse: {e}"));
}
