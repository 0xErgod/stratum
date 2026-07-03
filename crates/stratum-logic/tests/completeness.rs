//! Exact-vs-truncated model-checking verdicts (issue #4): a verdict over a
//! fully-explored finite LTS is definitive; over a truncated one it is only
//! about the explored fragment. Run extractors stay sound under truncation.

use stratum_core::term::{drop_, input, lift, output, par, quote, zero};
use stratum_core::{Name, Proc};
use stratum_lts::Lts;
use stratum_logic::examples::emits;
use stratum_logic::{counterexample, ef, holds_checked, neg, prop, satisfies_checked, witness};

/// The observable `goal` channel `@(@0!(0))`.
fn goal() -> Name {
    quote(lift(quote(zero()), zero()))
}

fn label(p: &str, s: &Proc) -> bool {
    match p {
        "goal" => emits(s, &goal()),
        _ => false,
    }
}

/// Finite, fully explorable: `@0!(0) | @0(y).goal!(0)` reduces once, then stops.
fn finite_system() -> Proc {
    let a = quote(zero());
    par([
        lift(a.clone(), zero()),
        input(a, move |_| lift(goal(), zero())),
    ])
}

/// Infinite-state (replication of `goal!(0)`) — truncates under a small bound.
fn replicating_system() -> Proc {
    fn replicator(c: Name) -> Proc {
        input(c.clone(), move |y| {
            par([output(c.clone(), y.clone()), drop_(y)])
        })
    }
    let self_c = quote(zero()); // internal replication channel @0
    let p = lift(goal(), zero()); // the replicated payload: goal!(0)
    par([
        lift(self_c.clone(), par([replicator(self_c.clone()), p])),
        replicator(self_c),
    ])
}

#[test]
fn finite_verdict_is_exact() {
    let lts = Lts::explore(&finite_system(), 100);
    assert!(!lts.is_truncated(), "a finite system should explore to completion");

    let v = holds_checked(&lts, &ef(prop("goal")), &label);
    assert!(v.holds, "goal is reachable");
    assert!(v.exact, "a fully-explored LTS gives a definitive verdict");
}

#[test]
fn truncated_verdict_is_not_exact() {
    let lts = Lts::explore(&replicating_system(), 4); // tiny bound -> truncates
    assert!(lts.is_truncated(), "replication should exceed a tiny bound");

    let v = holds_checked(&lts, &ef(prop("goal")), &label);
    assert!(v.holds, "goal is reached within the explored fragment");
    assert!(!v.exact, "a truncated LTS verdict is only about the fragment");
}

#[test]
fn witness_is_sound_under_truncation() {
    // A returned run is a genuine reachable path, definitive despite truncation.
    let lts = Lts::explore(&replicating_system(), 4);
    assert!(lts.is_truncated());

    let run = witness(&lts, &prop("goal"), &label).expect("goal is reached in the fragment");
    assert!(!run.is_empty(), "the witness is a concrete, real run");
    // The last state of the run genuinely emits on goal.
    let (_, last) = *run.last().unwrap();
    assert!(emits(lts.state(last), &goal()));
}

#[test]
fn satisfies_checked_reports_exactness_per_state() {
    // Finite system: exactly one (terminal) state emits goal; the verdict there
    // is definitive.
    let lts = Lts::explore(&finite_system(), 100);
    assert!(!lts.is_truncated());
    let goal_state = (0..lts.num_states())
        .find(|&i| emits(lts.state(i), &goal()))
        .expect("some state emits goal");
    let v = satisfies_checked(&lts, goal_state, &prop("goal"), &label);
    assert!(v.holds && v.exact);

    // Truncated system: exactness is false even for a state-local proposition.
    let tr = Lts::explore(&replicating_system(), 4);
    assert!(tr.is_truncated());
    let w = satisfies_checked(&tr, tr.initial(), &prop("goal"), &label);
    assert!(!w.exact);
}

#[test]
fn counterexample_to_safety_is_sound_under_truncation() {
    // A counterexample to a *safety* (universal) invariant found in the fragment
    // is a real bad run, definitive despite truncation. Here the invariant
    // "never goal" is violated because goal is reached.
    let lts = Lts::explore(&replicating_system(), 4);
    assert!(lts.is_truncated());
    let cex = counterexample(&lts, &neg(prop("goal")), &label)
        .expect("the safety invariant is violated within the fragment");
    let (_, bad) = *cex.last().unwrap();
    assert!(
        emits(lts.state(bad), &goal()),
        "the counterexample ends at a real goal-emitting state"
    );
}
