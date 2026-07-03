//! Fair-CTL tests: liveness (`fair_af`) under a generalized-Büchi fairness
//! condition (the ϕ↔fairness bridge).
//!
//! The centrepiece is a ρ-calculus *scheduler* that is **live only under
//! fairness**. From its neutral state it can idle on a self-loop forever, or
//! advance through an intermediate `ready`-emitting state to a
//! `progress`-emitting state and back. Plain `AF(progress)` is false — the idle
//! self-loop starves progress. The fairness constraint "visit `ready` infinitely
//! often" — a predicate *distinct* from the `progress` goal — rules out that idle
//! run, so every fair run must advance through `ready`, and hence reach
//! `progress`; `fair_af(progress)` is then true. The constraint does real
//! scheduling work: it is not the goal (that would be vacuously true for any
//! system) but an upstream state the goal is reachable through.

use stratum_core::term::{drop_, input, lift, par, quote, zero};
use stratum_core::{Name, Proc};
use stratum_logic::examples::emits;
use stratum_logic::{
    af, check, check_fair, eg, fair_af, fair_eg, holds, holds_fair, prop, tt, Fairness,
};
use stratum_lts::Lts;

/// Shared duplicator / idle channel `a` (`@0`).
fn chan_a() -> Name {
    quote(zero())
}
/// Intermediate `ready` channel (`@(@0!(0))`) — distinct from `a`.
fn chan_ready() -> Name {
    quote(lift(quote(zero()), zero()))
}
/// Goal `progress` channel (`@(@0!(@0!(0)))`) — distinct from `a` and `ready`.
fn chan_progress() -> Name {
    quote(lift(quote(zero()), lift(quote(zero()), zero())))
}

/// `Rc = a(y).(*y | a⟨|*y|⟩)` — the shared receiver on `a`: a duplicator that,
/// on firing, both *runs* the received code (`*y`) and *re-sends* it
/// (`a⟨|*y|⟩`). Which lift it consumes selects idle vs. advance.
fn rc() -> Proc {
    input(chan_a(), |y| {
        par([drop_(y.clone()), lift(chan_a(), drop_(y))])
    })
}

/// `Seq = ready⟨|0|⟩ | ready(z).(progress⟨|0|⟩ | progress(w).Rc)` — the advance
/// payload.
///
/// Run in stages: it emits `ready`, then (consuming its own `ready`) emits
/// `progress`, then (consuming its own `progress`) rebuilds the receiver `Rc`.
/// Each marker is *consumed* as the next stage fires, so markers never
/// accumulate. It rebuilds only `Rc` — not the `a`-lift — because the advance
/// step leaves the neutral state's other `a`-lift untouched, so the cycle closes
/// back to exactly `s0` (a finite three-state graph).
fn seq() -> Proc {
    par([
        lift(chan_ready(), zero()),
        input(chan_ready(), |_z| {
            par([
                lift(chan_progress(), zero()),
                input(chan_progress(), |_w| rc()),
            ])
        }),
    ])
}

/// `a⟨|Rc|⟩ | a⟨|Seq|⟩ | Rc` — the neutral scheduler state `s0`.
///
/// `Rc` can fire with either `a`-lift: consuming `a⟨|Rc|⟩` rebuilds `s0` (an idle
/// self-loop), while consuming `a⟨|Seq|⟩` enters the `ready → progress → s0`
/// advance cycle.
fn scheduler() -> Proc {
    par([lift(chan_a(), rc()), lift(chan_a(), seq()), rc()])
}

/// `a⟨|Rc|⟩ | Rc` — a bare idle self-loop on `a`: one `Comm` reproduces the same
/// state. Never emits `ready` or `progress`.
fn idle_loop() -> Proc {
    par([lift(chan_a(), rc()), rc()])
}

/// A system that deadlocks in `¬progress`: `ready⟨|0|⟩ | ready(_).0 → 0`. Reaches
/// a terminal state that never emits `progress` — the shape that exercises the
/// deadlock-awareness of `af` / `fair_af`.
fn deadlocks_without_progress() -> Proc {
    par([lift(chan_ready(), zero()), input(chan_ready(), |_| zero())])
}

/// Labelling: `ready` / `progress` hold where the respective marker channel has a
/// pending emit.
fn labeller() -> impl Fn(&str, &Proc) -> bool {
    let ready = chan_ready();
    let progress = chan_progress();
    move |p: &str, proc: &Proc| match p {
        "ready" => emits(proc, &ready),
        "progress" => emits(proc, &progress),
        _ => false,
    }
}

/// The scheduler explores to exactly three states with the intended shape:
/// s0 neutral (idle self-loop + advance), s1 `ready` (forced onward), s2
/// `progress` (forced back to s0). The `ready` state is *transient* — its only
/// successor is `progress` — which is what lets the `ready` constraint force
/// liveness.
#[test]
fn scheduler_shape() {
    let lts = Lts::explore(&scheduler(), 100);
    let label = labeller();
    assert!(!lts.is_truncated(), "state space is finite");
    assert_eq!(lts.num_states(), 3, "neutral, ready, progress");

    let init = lts.initial();
    // s0: neutral, with an idle self-loop AND an advancing edge.
    assert!(!label("ready", lts.state(init)) && !label("progress", lts.state(init)));
    assert!(
        lts.transitions(init).iter().any(|t| t.target == init),
        "s0 has an idle self-loop (the starving run)"
    );
    let ready_state = lts
        .transitions(init)
        .iter()
        .map(|t| t.target)
        .find(|&t| t != init)
        .expect("s0 can advance");
    // s1: ready, transient — its sole successor is the progress state.
    assert!(label("ready", lts.state(ready_state)));
    assert!(!label("progress", lts.state(ready_state)));
    assert_eq!(lts.transitions(ready_state).len(), 1, "ready is transient");
    let progress_state = lts.transitions(ready_state)[0].target;
    assert!(label("progress", lts.state(progress_state)));
}

/// The required acceptance property: **live only under fairness**, with a
/// non-circular constraint (`ready` ≠ `progress`).
///
/// Plain `AF(progress)` is false — the idle self-loop starves progress. Under the
/// fairness constraint "visit `ready` infinitely often", the starving run (which
/// never enters `ready`) is unfair, so every fair run advances through `ready` to
/// `progress`, and `fair_af(progress)` is true.
#[test]
fn live_only_with_fairness_via_distinct_constraint() {
    let lts = Lts::explore(&scheduler(), 100);
    let label = labeller();
    // The scheduling constraint is on `ready`, a state distinct from the goal.
    let fairness = Fairness::new().constrain(prop("ready"));

    assert!(
        !holds(&lts, &af(prop("progress")), &label),
        "without fairness, the idle self-loop starves progress"
    );
    assert!(
        holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "under `visit ready i.o.`, every fair run advances to progress"
    );

    // Sanity that the constraint is doing real work and the witness is not
    // vacuous: a fair path genuinely exists here (fairEG ⊤ under {ready} holds),
    // so `fair_af` is true non-vacuously.
    assert!(
        holds_fair(&lts, &fair_eg(tt()), &label, &fairness),
        "a fair (ready-visiting) infinite run exists"
    );
}

/// Fairness must not rescue a genuinely non-live system: `progress` is never
/// reachable, yet a fair infinite run (the idle loop, which satisfies the `⊤`
/// constraint) starves it forever. `fair_af(progress)` stays false — this is
/// *not* the vacuous "no fair path" case.
#[test]
fn not_live_stays_false_under_fairness() {
    let lts = Lts::explore(&idle_loop(), 100);
    let label = labeller();
    let fairness = Fairness::new().constrain(tt());

    assert!(!holds(&lts, &af(prop("progress")), &label));
    assert!(
        holds_fair(&lts, &fair_eg(tt()), &label, &fairness),
        "a fair run exists (the idle loop)"
    );
    assert!(
        !holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "that fair run starves progress, so fairness cannot make it live"
    );
}

/// `ready⟨|0|⟩ | ready(_).progress⟨|0|⟩` — a deterministic system that always
/// reaches `progress`. It is live *without* fairness, and adding fairness must
/// not flip that verdict (fair paths are a subset of all paths).
#[test]
fn fairness_preserves_already_live() {
    let progress = chan_progress();
    let sys = par([
        lift(chan_ready(), zero()),
        input(chan_ready(), move |_| lift(progress.clone(), zero())),
    ]);
    let lts = Lts::explore(&sys, 100);
    let label = labeller();
    let fairness = Fairness::new().constrain(prop("ready"));

    assert!(
        holds(&lts, &af(prop("progress")), &label),
        "already live without fairness"
    );
    assert!(
        holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "fairness does not wrongly flip an already-live system"
    );
}

/// With **zero** fairness constraints, `fair_eg φ` coincides with plain `eg φ` on
/// every state — checked on a looping system (scheduler) and a deadlocking one.
#[test]
fn empty_fairness_fair_eg_equals_eg() {
    let empty = Fairness::new();
    let label = labeller();
    for sys in [scheduler(), deadlocks_without_progress()] {
        let lts = Lts::explore(&sys, 100);
        for phi in [tt(), prop("progress")] {
            assert_eq!(
                check_fair(&lts, &fair_eg(phi.clone()), &label, &empty),
                check(&lts, &eg(phi.clone()), &label),
                "fair_eg with no constraints must equal eg"
            );
        }
    }
}

/// With **zero** fairness constraints, `fair_af φ` coincides with the
/// deadlock-aware plain `af φ` on **all** reachable states. Includes a system
/// that deadlocks in `¬progress`, so the deadlock-awareness disjunct is exercised
/// (there `fair_af(progress)` must be false, not vacuously true).
#[test]
fn empty_fairness_fair_af_equals_af_including_deadlock() {
    let empty = Fairness::new();
    let label = labeller();
    for sys in [scheduler(), deadlocks_without_progress()] {
        let lts = Lts::explore(&sys, 100);
        let fair = check_fair(&lts, &fair_af(prop("progress")), &label, &empty);
        let plain = check(&lts, &af(prop("progress")), &label);
        assert_eq!(
            fair, plain,
            "fair_af with no constraints must equal af on every state"
        );
    }

    // Pin the deadlock case explicitly: af is false at the initial state because
    // a maximal run terminates in ¬progress, and fair_af agrees (not vacuous).
    let lts = Lts::explore(&deadlocks_without_progress(), 100);
    assert!(!holds(&lts, &af(prop("progress")), &label));
    assert!(!holds_fair(
        &lts,
        &fair_af(prop("progress")),
        &label,
        &empty
    ));
}
