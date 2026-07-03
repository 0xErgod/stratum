//! Correspondence checks for the [`stratum::encodings`] standard library.
//!
//! These validate the §3 replication encoding *experimentally* — they run the
//! macro's desugaring through the real reduction/LTS/equivalence machinery on
//! concrete instances, rather than asserting a paper claim. Two things are
//! demonstrated:
//!
//! * **Transparency.** `expand(bang(0))` is verbatim the raw §3 term — no
//!   `def`/`new`/`bang` sugar, the internal channel made explicit.
//! * **Operational correspondence (Gorla-style, informally).** For the source
//!   term `S = P` and its translation `[[S]] = bang(P)`:
//!   - *Completeness / soundness on `P = 0`:* `bang(0)` and `0` are weak
//!     N-barbed bisimilar **exactly when** the internal channel `x` is not
//!     observed. The only behaviour `bang(0)` adds over `0` is an internal
//!     `τ`-loop on `x`; hide `x` and the two are `≈N`, observe `x` and they are
//!     told apart. This is the "translation preserves & reflects behaviour up to
//!     the freshly-restricted names" leg of a Gorla criterion, made concrete.
//!   - *Divergence-as-replication:* `bang(P)` for an observable, inert `P`
//!     accumulates copies of `P` monotonically — the encoding really does
//!     replicate, one copy per internal step.

use stratum::core::{lift, name_equiv, quote, zero, Name, Proc};
use stratum::encodings::with_stdlib;
use stratum::equiv::{may_barbs, weak_barbed_bisimilar, Verdict};
use stratum::lts::Lts;
use stratum::syntax::{expand, parse};

/// The top-level parallel components of a process.
fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Par(ps) => ps.iter().collect(),
        Proc::Zero => Vec::new(),
        other => vec![other],
    }
}

/// The internal channel `x` that `bang`'s `new` minted: the channel of the
/// top-level lift `x!(…)` in the desugared engine. Extracted structurally so
/// the tests do not hard-code the ground-name assignment.
fn internal_channel(bang_p: &Proc) -> Name {
    for c in components(bang_p) {
        if let Proc::Lift { chan, .. } = c {
            return chan.clone();
        }
    }
    panic!("bang(...) should have a top-level lift on its internal channel");
}

/// How many top-level `chan!(…)` outputs a process has (copy counter).
fn count_lifts_on(p: &Proc, chan: &Name) -> usize {
    components(p)
        .iter()
        .filter(|c| matches!(c, Proc::Lift { chan: ch, .. } if name_equiv(ch, chan)))
        .count()
}

// --- transparency -----------------------------------------------------------

#[test]
fn bang_expand_is_the_section3_machinery() {
    // The verbatim desugaring a reviewer eyeballs: the message carries the
    // replicator `B = x(y).(x!(*y) | *y)` together with `P` (here `0`), and a
    // co-located copy of `B` waits to consume it. `x` is minted as `@0`.
    let raw = expand(&with_stdlib("bang(0)")).unwrap();
    assert_eq!(
        raw,
        "@0!(@0(v0).(@0!(*v0) | *v0) | 0) | @0(v1).(@0!(*v1) | *v1)",
    );
    // And it is faithful: re-parses to the same closed core term.
    assert!(parse(&raw).unwrap().is_closed());
}

#[test]
fn bang_of_a_process_carries_that_process() {
    // `bang(P)` threads `P` verbatim into the replicated message.
    let raw = expand(&with_stdlib("bang( @(@0!(0))!(0) )")).unwrap();
    assert_eq!(
        raw,
        "@0!(@0(v0).(@0!(*v0) | *v0) | @(@0!(0))!(0)) | @0(v1).(@0!(*v1) | *v1)",
    );
}

// --- operational correspondence: replication of 0 is invisible off `x` ------

#[test]
fn bang_null_is_null_up_to_the_internal_channel() {
    // `bang(0)` desugars to a single self-looping state: `x!(B) | B → x!(B) | B`.
    let b0 = parse(&with_stdlib("bang(0)")).unwrap();
    let nil = parse("0").unwrap();

    let lts = Lts::explore(&b0, 50);
    assert_eq!(lts.num_states(), 1, "bang(0) is a single τ-looping state");
    assert!(!lts.is_truncated());
    assert_eq!(lts.transitions(0).len(), 1, "the loop on the internal channel");

    let x = internal_channel(&b0);

    // Hide `x` (observe nothing, or anything other than `x`): the only
    // difference between bang(0) and 0 is the internal loop, so they are ≈N.
    assert_eq!(
        weak_barbed_bisimilar(&b0, &nil, &[], 50),
        Verdict::Equivalent,
        "bang(0) ≈N 0 when the internal channel is not observed",
    );

    // Observe `x`: bang(0) has a barb there, 0 does not — they are distinguished.
    let verdict = weak_barbed_bisimilar(&b0, &nil, std::slice::from_ref(&x), 50);
    assert!(
        matches!(verdict, Verdict::Distinguished(_)),
        "observing the internal channel must distinguish bang(0) from 0, got {verdict:?}",
    );
}

// --- operational correspondence: bang really replicates ---------------------

#[test]
fn bang_accumulates_copies_of_an_inert_process() {
    // `s` is minted first (top-level `new`), so `s = @0` is observable and the
    // engine's internal `x` is a *different*, later ground name. Each internal
    // step spawns one more inert `s!(0)`, so the reachable states form a chain
    // whose k-th node carries exactly k copies.
    let bang_s = parse(&with_stdlib("new s\nbang( s!(0) )")).unwrap();
    let s = quote(zero()); // @0

    let bound = 8;
    let lts = Lts::explore(&bang_s, bound);
    assert_eq!(lts.num_states(), bound);
    assert!(lts.is_truncated(), "replication is unbounded: the chain is infinite");

    let mut counts: Vec<usize> = (0..lts.num_states())
        .map(|i| count_lifts_on(lts.state(i), &s))
        .collect();
    counts.sort_unstable();
    assert_eq!(
        counts,
        (0..bound).collect::<Vec<_>>(),
        "each reachable state carries one more copy of P than the previous",
    );

    // Sanity: `s` really is a weak barb (the copies are observable outputs).
    let (barbs, _) = may_barbs(&bang_s, std::slice::from_ref(&s), bound);
    assert!(barbs.iter().any(|b| name_equiv(b, &s)));
}

// --- contract: input-guarded replication ------------------------------------

#[test]
fn contract_expands_through_bang() {
    // `contract(C, P)` is `bang( C(y).P )`: transparent, and still just core.
    let raw = expand(&with_stdlib("new c\ncontract(c, 0)")).unwrap();
    assert!(!raw.contains("contract") && !raw.contains("bang"));
    assert!(!raw.contains("def") && !raw.contains("new"));
    assert!(parse(&raw).unwrap().is_closed());
}

#[test]
fn contract_fires_its_guarded_body_on_each_message() {
    // A persistent server on `c` whose guard emits a signal on `sig`; one client
    // message on `c` should let the signal become observable.
    //
    // `c = @0`, `sig = @(@0!(0))` (minted in that order); the engine's channels
    // are later ground names. The state space is infinite (bang spawns inputs
    // eagerly), so we use `may_barbs`: the barbs it returns are genuinely
    // reachable even when exploration is truncated.
    let src = with_stdlib("new c, sig\ncontract(c, sig!(0)) | c!(0)");
    let p = parse(&src).unwrap();
    let sig = quote(lift(quote(zero()), zero())); // @(@0!(0))

    let (barbs, _truncated) = may_barbs(&p, std::slice::from_ref(&sig), 300);
    assert!(
        barbs.iter().any(|b| name_equiv(b, &sig)),
        "a message on the contract channel must make the guarded body's barb observable",
    );
}
