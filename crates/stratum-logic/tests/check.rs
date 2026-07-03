//! Model-checking tests over ρ-calculus systems.

use stratum_core::term::{input, lift, quote, zero, par};
use stratum_core::{Name, Proc};
use stratum_lts::Lts;
use stratum_logic::examples::emits;
use stratum_logic::{af, ag, can, ef, eg, holds, neg, tt, prop, witness, counterexample};

/// Distinct channels used across the tests.
fn chan_a() -> Name {
    quote(zero()) // @0
}
fn chan_done() -> Name {
    quote(lift(quote(zero()), zero())) // @(@0!(0)) — distinct from @0
}

/// Labelling: "done" holds where the system has a pending output on `done`.
fn labeller() -> impl Fn(&str, &Proc) -> bool {
    let done = chan_done();
    move |p: &str, proc: &Proc| match p {
        "done" => emits(proc, &done),
        "any" => true,
        _ => false,
    }
}

/// `a⟨|0|⟩ | a(y).done⟨|0|⟩` — one Comm, then the system emits on `done`.
fn emitting_system() -> Proc {
    let done = chan_done();
    par([
        lift(chan_a(), zero()),
        input(chan_a(), move |_| lift(done.clone(), zero())),
    ])
}

/// Reachability: `EF done` holds and a witness of length 1 exists; `done` is not
/// yet true initially so `AG done` fails.
#[test]
fn reachability_and_witness() {
    let lts = Lts::explore(&emitting_system(), 100);
    let label = labeller();

    assert!(holds(&lts, &ef(prop("done")), &label));
    assert!(!holds(&lts, &ag(prop("done")), &label));

    let w = witness(&lts, &prop("done"), &label).expect("done is reachable");
    assert_eq!(w.len(), 1, "one Comm reaches the emitting state");
}

/// Safety with a counterexample: the invariant `AG ¬done` fails, and the checker
/// produces a shortest run to the violating state.
#[test]
fn safety_counterexample() {
    let lts = Lts::explore(&emitting_system(), 100);
    let label = labeller();

    // The per-state invariant we want: "never emits done".
    let safe = neg(prop("done"));
    // As a temporal property, `AG safe` fails.
    assert!(!holds(&lts, &ag(safe.clone()), &label));

    // `counterexample` takes the per-state invariant and finds a reachable
    // state where it breaks.
    let cex = counterexample(&lts, &safe, &label).expect("invariant is violated");
    assert_eq!(cex.len(), 1);
    // The final state of the counterexample really does emit on `done`.
    let (_, bad) = cex.last().unwrap();
    assert!(emits(lts.state(*bad), &chan_done()));
}

/// Liveness that holds: every path of the deterministic emitting system reaches
/// `done`, so `AF done` is true.
#[test]
fn liveness_holds() {
    let lts = Lts::explore(&emitting_system(), 100);
    assert!(holds(&lts, &af(prop("done")), &labeller()));
}

/// Liveness that fails, deadlock-aware: with a nondeterministic choice, one
/// branch deadlocks at `0` without ever emitting `done`, so `AF done` is false.
#[test]
fn liveness_fails_on_deadlocking_branch() {
    let done = chan_done();
    // a⟨|0|⟩ | a(_).0 | a(_).done⟨|0|⟩ : the send reacts with either receiver.
    let sys = par([
        lift(chan_a(), zero()),
        input(chan_a(), |_| zero()),
        input(chan_a(), move |_| lift(done.clone(), zero())),
    ]);
    let lts = Lts::explore(&sys, 100);

    // Sanity: there really is a deadlocking branch (a terminal state not emitting).
    let terminals_without_done = (0..lts.num_states())
        .filter(|&i| lts.is_terminal(i) && !emits(lts.state(i), &chan_done()))
        .count();
    assert!(terminals_without_done >= 1);

    assert!(!holds(&lts, &af(prop("done")), &labeller()));
}

/// Greatest-fixpoint sanity: on a system whose every run terminates, `EG ⊤`
/// (an infinite path exists) is false at the initial state.
#[test]
fn no_infinite_path() {
    let lts = Lts::explore(&emitting_system(), 100);
    assert!(!holds(&lts, &eg(tt()), &labeller()));
}

/// Action-indexed modality: initially a Comm on channel `a` is possible, but not
/// on channel `done`.
#[test]
fn action_indexed_modality() {
    let lts = Lts::explore(&emitting_system(), 100);
    let label = labeller();
    assert!(holds(&lts, &can(chan_a()), &label));
    assert!(!holds(&lts, &can(chan_done()), &label));
}
