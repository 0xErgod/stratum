//! Tests for N-barbed bisimulation and may-testing equivalence.

use stratum_core::term::{input, lift, par, quote, zero};
use stratum_core::Name;
use stratum_equiv::{may_equivalent, strong_barbed_bisimilar, weak_barbed_bisimilar, Verdict};

/// Observable channel `x = @0`.
fn x() -> Name {
    quote(zero())
}
/// A private/internal channel `a`, distinct from `x` and not observed.
fn a() -> Name {
    quote(lift(quote(zero()), zero())) // @(@0!(0))
}

/// `x⟨|0|⟩` — barbs on `x` immediately.
fn emits_now() -> stratum_core::Proc {
    lift(x(), zero())
}

/// `a⟨|0|⟩ | a(y).x⟨|0|⟩` — barbs on `x` only after one internal step.
fn emits_after_tau() -> stratum_core::Proc {
    par([lift(a(), zero()), input(a(), move |_| lift(x(), zero()))])
}

/// Weak bisimulation ignores the internal step: emitting now and emitting after
/// one τ are `≈N` for `N = {x}`.
#[test]
fn weak_ignores_internal_step() {
    let obs = [x()];
    assert!(weak_barbed_bisimilar(&emits_now(), &emits_after_tau(), &obs, 100).is_equivalent());
}

/// Strong bisimulation does *not* ignore it: the internal step is a real
/// difference, so the two are distinguished strongly.
#[test]
fn strong_sees_internal_step() {
    let obs = [x()];
    let v = strong_barbed_bisimilar(&emits_now(), &emits_after_tau(), &obs, 100);
    assert!(matches!(v, Verdict::Distinguished(_)), "got {v:?}");
}

/// A process that can never barb `x` is distinguished from one that does, even
/// weakly.
#[test]
fn distinct_observable_behavior() {
    let obs = [x()];
    let v = weak_barbed_bisimilar(&emits_now(), &zero(), &obs, 100);
    assert!(matches!(v, Verdict::Distinguished(_)), "got {v:?}");
}

/// Bisimulation is reflexive.
#[test]
fn reflexive() {
    let obs = [x()];
    assert!(
        weak_barbed_bisimilar(&emits_after_tau(), &emits_after_tau(), &obs, 100).is_equivalent()
    );
    assert!(strong_barbed_bisimilar(&emits_now(), &emits_now(), &obs, 100).is_equivalent());
}

/// Observation set matters: with nothing observed the two emitters agree; but
/// against a non-emitter, may-testing still separates on `{x}`.
#[test]
fn may_testing() {
    let obs = [x()];
    assert!(may_equivalent(&emits_now(), &emits_after_tau(), &obs, 100).is_equivalent());

    let v = may_equivalent(&emits_now(), &zero(), &obs, 100);
    assert!(matches!(v, Verdict::Distinguished(_)), "got {v:?}");
}

/// Strong bisimilarity implies weak: any strongly-equivalent pair is weakly
/// equivalent too (sanity on a reflexive pair with internal steps).
#[test]
fn strong_implies_weak() {
    let obs = [x()];
    let p = emits_after_tau();
    if strong_barbed_bisimilar(&p, &p, &obs, 100).is_equivalent() {
        assert!(weak_barbed_bisimilar(&p, &p, &obs, 100).is_equivalent());
    }
}

/// Infinite state space (replication) yields an inconclusive verdict under a
/// tight bound rather than a wrong answer.
#[test]
fn truncation_is_inconclusive() {
    use stratum_core::term::{drop_, output};
    fn replicator(c: Name) -> stratum_core::Proc {
        input(c.clone(), move |y| {
            par([output(c.clone(), y.clone()), drop_(y)])
        })
    }
    let c = x();
    let p = lift(quote(drop_(quote(zero()))), zero());
    let bang = par([
        lift(c.clone(), par([replicator(c.clone()), p])),
        replicator(c),
    ]);

    let v = weak_barbed_bisimilar(&bang, &zero(), &[x()], 5);
    assert!(matches!(v, Verdict::Inconclusive(_)), "got {v:?}");
}
