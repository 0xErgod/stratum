//! Fair-CTL tests: liveness (`fair_af`) under a generalized-Büchi fairness
//! condition (the ϕ↔fairness bridge).
//!
//! The centrepiece is a ρ-calculus system that is **live only under fairness**:
//! an idle self-loop can starve a repeatedly-enabled `progress` action forever,
//! so plain `AF(progress)` is false; a fairness constraint that rules out the
//! starving run makes every fair run reach `progress`, so `fair_af(progress)` is
//! true.

use stratum_core::term::{drop_, input, lift, par, quote, zero};
use stratum_core::{Name, Proc};
use stratum_logic::examples::emits;
use stratum_logic::{af, fair_af, holds, holds_fair, prop, tt, Fairness};
use stratum_lts::Lts;

/// Idle-loop channel `a` (`@0`).
fn chan_a() -> Name {
    quote(zero())
}
/// Trigger channel `c` (`@(@0!(0))`) — distinct from `a`.
fn chan_c() -> Name {
    quote(lift(quote(zero()), zero()))
}
/// Observable `progress` channel (`@(@0!(@0!(0)))`) — distinct from `a` and `c`.
fn chan_progress() -> Name {
    quote(lift(quote(zero()), lift(quote(zero()), zero())))
}

/// `K = a(y).(*y | a⟨|*y|⟩)` — the ρ-calculus replication/duplicator prefix.
///
/// Received code is both *run* (`*y`) and *re-sent* (`a⟨|*y|⟩`), which is what
/// makes [`idle_loop`] reproduce itself.
fn k() -> Proc {
    input(chan_a(), |y| {
        par([drop_(y.clone()), lift(chan_a(), drop_(y))])
    })
}

/// `a⟨|K|⟩ | K` — a self-loop on channel `a`: one `Comm` reproduces the same
/// state (`→ K | a⟨|K|⟩`), giving an infinite "idle" run in a single LTS state.
fn idle_loop() -> Proc {
    par([lift(chan_a(), k()), k()])
}

/// Labelling: `progress` holds where the system has a pending emit on the
/// `progress` channel.
fn labeller() -> impl Fn(&str, &Proc) -> bool {
    let progress = chan_progress();
    move |p: &str, proc: &Proc| match p {
        "progress" => emits(proc, &progress),
        _ => false,
    }
}

/// `idle_loop | c⟨|0|⟩ | c(_).progress⟨|0|⟩`
///
/// The initial state has two redexes: the idle self-loop on `a` (which starves
/// `progress`) and the one-shot `c`-`Comm` that emits `progress`. So there is an
/// infinite unfair run (loop on `a` forever) that never makes progress.
fn live_only_under_fairness() -> Proc {
    let progress = chan_progress();
    par([
        idle_loop(),
        lift(chan_c(), zero()),
        input(chan_c(), move |_| lift(progress.clone(), zero())),
    ])
}

/// The idle self-loop really is a self-loop, and the system explores to exactly
/// two states (idle; idle-with-progress-emitted).
#[test]
fn system_shape_is_a_starving_self_loop() {
    let lts = Lts::explore(&live_only_under_fairness(), 100);
    assert!(!lts.is_truncated(), "state space is finite");
    assert_eq!(lts.num_states(), 2, "s0 (starving) and s1 (progress)");

    let init = lts.initial();
    // s0 self-loops (the unfair, progress-starving run) ...
    assert!(
        lts.transitions(init).iter().any(|t| t.target == init),
        "initial state has an idle self-loop"
    );
    // ... and can also step to the progress state.
    let progress = chan_progress();
    assert!(
        lts.transitions(init)
            .iter()
            .any(|t| emits(lts.state(t.target), &progress)),
        "initial state can reach a progress-emitting state"
    );
}

/// The required acceptance property: **live only under fairness**.
///
/// Plain `AF(progress)` is false — the idle self-loop is an infinite run that
/// never reaches `progress`. Under the fairness constraint "visit `progress`
/// states infinitely often", that starving run is excluded, so every fair run
/// reaches `progress` and `fair_af(progress)` is true.
#[test]
fn live_only_with_fairness() {
    let lts = Lts::explore(&live_only_under_fairness(), 100);
    let label = labeller();
    let fairness = Fairness::new().constrain(prop("progress"));

    assert!(
        !holds(&lts, &af(prop("progress")), &label),
        "without fairness, the idle self-loop starves progress"
    );
    assert!(
        holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "under fairness, every fair run reaches progress"
    );
}

/// Fairness must not rescue a genuinely non-live system: here `progress` is never
/// reachable, yet a fair infinite run (the idle loop, which trivially satisfies
/// the `⊤` fairness constraint) starves it forever. `fair_af(progress)` stays
/// false — this is *not* the vacuous "no fair path" case.
#[test]
fn not_live_stays_false_under_fairness() {
    let lts = Lts::explore(&idle_loop(), 100);
    let label = labeller();
    // A fair path exists (the idle loop visits ⊤ infinitely often) but never
    // makes progress.
    let fairness = Fairness::new().constrain(tt());

    assert!(!holds(&lts, &af(prop("progress")), &label));
    assert!(
        !holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "a fair run starves progress, so fairness cannot make it live"
    );
}

/// `c⟨|0|⟩ | c(_).progress⟨|0|⟩` — a deterministic system that always reaches
/// `progress`. It is live *without* fairness, and adding fairness must not flip
/// that verdict (fair paths are a subset of all paths).
#[test]
fn fairness_preserves_already_live() {
    let progress = chan_progress();
    let sys = par([
        lift(chan_c(), zero()),
        input(chan_c(), move |_| lift(progress.clone(), zero())),
    ]);
    let lts = Lts::explore(&sys, 100);
    let label = labeller();
    let fairness = Fairness::new().constrain(prop("progress"));

    assert!(
        holds(&lts, &af(prop("progress")), &label),
        "already live without fairness"
    );
    assert!(
        holds_fair(&lts, &fair_af(prop("progress")), &label, &fairness),
        "fairness does not wrongly flip an already-live system"
    );
}
