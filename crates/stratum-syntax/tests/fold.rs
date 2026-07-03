//! Integration tests for the alias-folding printer ([`to_source_folded`]) and
//! the [`parse_with_aliases`] dictionary it consumes.
//!
//! Folding is the readable/backward complement of [`to_source`] (the raw view):
//! it prints a term using the source's `def`/`new` names wherever a channel's
//! canonical form matches, and falls back to the explicit `@…` quote otherwise.
//! It is *pure presentation* — the returned [`Proc`] is exactly what [`parse`]
//! yields — and the folded string is for **reading, not re-parsing**.

use stratum_core::structurally_congruent;
use stratum_syntax::{parse, parse_with_aliases, to_source, to_source_folded};

#[test]
fn parse_with_aliases_matches_parse() {
    // The returned process is identical (≡) to plain `parse`; only the extra
    // dictionary is new.
    let src = "new req, ack\nreq!(0) | req(x).ack!(0)";
    let (p, _aliases) = parse_with_aliases(src).unwrap();
    assert!(structurally_congruent(&p, &parse(src).unwrap()));
}

#[test]
fn folds_new_names_raw_spells_them_out() {
    // `new req, ack` → req = @0, ack = @(@0!(0)). Folded prints the source
    // names; raw prints the ground quotes.
    let src = "new req, ack\nreq!(0) | req(x).ack!(0)";
    let (p, aliases) = parse_with_aliases(src).unwrap();

    assert_eq!(to_source_folded(&p, &aliases), "req!(0) | req(v0).ack!(0)");
    assert_eq!(to_source(&p), "@0!(0) | @0(v0).@(@0!(0))!(0)");
}

#[test]
fn only_aliased_names_fold_raw_quote_stays() {
    // `ack` aliases the non-`@0` ground name @(@0!(0)); the program mixes it with
    // a raw `@0` that has no `def`/`new` behind it. Only the aliased channel
    // folds; the raw `@0` is left as an explicit quote.
    let src = "def ack { @(@0!(0)) }\nack!(0) | @0!(0)";
    let (p, aliases) = parse_with_aliases(src).unwrap();

    let folded = to_source_folded(&p, &aliases);
    // The aliased channel folds whole (no inner @0 leaks through)...
    assert!(folded.contains("ack!(0)"), "alias not folded: {folded}");
    // ...while the raw `@0` stays a bare quote.
    assert!(folded.contains("@0!(0)"), "raw quote lost: {folded}");
    assert_eq!(folded, "ack!(0) | @0!(0)");
    // Raw view folds nothing: both channels spelled out in full.
    assert_eq!(to_source(&p), "@(@0!(0))!(0) | @0!(0)");
}

#[test]
fn folds_name_shaped_def_alias() {
    // A name-shaped `def` alias folds too, not just `new` names.
    let src = "def z { @0 }\nz!(0) | z(x).*x";
    let (p, aliases) = parse_with_aliases(src).unwrap();

    let folded = to_source_folded(&p, &aliases);
    assert_eq!(folded, "z!(0) | z(v0).*v0");
    assert!(aliases.get(&stratum_core::term::quote(stratum_core::term::zero())) == Some("z"));
}

#[test]
fn folded_output_contains_alias_names_not_reparseable() {
    // Round-trip sanity: the folded string is for reading. Re-parsing it fails
    // because the `new`/`def` preamble that would bind the aliases is gone — so
    // we assert the folded text *contains the alias identifiers* instead.
    let src = "new req, ack\nreq!(0) | req(x).ack!(0)";
    let (p, aliases) = parse_with_aliases(src).unwrap();
    let folded = to_source_folded(&p, &aliases);

    assert!(folded.contains("req"), "missing `req`: {folded}");
    assert!(folded.contains("ack"), "missing `ack`: {folded}");
    // No `@…` quote survives once every channel folds.
    assert!(!folded.contains('@'), "a quote leaked: {folded}");
    // And re-parsing the folded (unsugared) form is expected to fail: the
    // aliases are now unbound identifiers.
    assert!(parse(&folded).is_err(), "folded form should not re-parse: {folded}");

    // The raw form, by contrast, always re-parses (≡ the original).
    let raw = to_source(&p);
    assert!(structurally_congruent(&parse(&raw).unwrap(), &p));
}

#[test]
fn no_aliases_folded_equals_raw() {
    // With no `def`/`new` names, the dictionary is empty and folding is a no-op:
    // `to_source_folded` coincides with `to_source`.
    let src = "@0!(0) | @0(y).(*y | @0!(0))";
    let (p, aliases) = parse_with_aliases(src).unwrap();
    assert!(aliases.is_empty());
    assert_eq!(to_source_folded(&p, &aliases), to_source(&p));
}
