//! Epistemic tests: the `K_A` / `P_A` operators over agents' information fields
//! (the σ↔ϕ bridge).

use stratum_core::term::{input, lift, par, quote, zero};
use stratum_core::Name;
use stratum_field::observational_field;
use stratum_logic::examples::emits;
use stratum_logic::{check, check_epistemic, knows, possible, prop, Agents};
use stratum_lts::Lts;

fn pub_() -> Name {
    quote(zero()) // @0 — public channel
}
fn hidden() -> Name {
    quote(lift(quote(zero()), zero())) // @(@0!(0)) — secret channel
}
fn c() -> Name {
    // @(@0!(@0!(0))) — internal choice channel; a quoted *lift* (not a quoted
    // drop), so quote-drop does not collapse it onto `pub` or `hidden`.
    quote(lift(quote(zero()), lift(quote(zero()), zero())))
}

/// `c⟨|0|⟩ | c(_).pub⟨|0|⟩ | c(_).(pub⟨|0|⟩ | hidden⟨|0|⟩)`
///
/// The internal choice on `c` leads to one of two outcomes that *both* emit on
/// `pub` but differ on `hidden`. An agent watching only `pub` cannot tell them
/// apart; an agent watching `hidden` can.
fn system() -> stratum_core::Proc {
    let p = pub_();
    let h = hidden();
    par([
        lift(c(), zero()),
        input(c(), {
            let p = p.clone();
            move |_| lift(p.clone(), zero())
        }),
        input(c(), move |_| {
            par([lift(p.clone(), zero()), lift(h.clone(), zero())])
        }),
    ])
}

fn agents(lts: &Lts) -> Agents {
    let mut m = Agents::new();
    // A sees only `pub`; B sees both `pub` and `hidden`.
    m.insert("A".to_string(), observational_field(lts, &[pub_()]));
    m.insert(
        "B".to_string(),
        observational_field(lts, &[pub_(), hidden()]),
    );
    m
}

fn label(p: &str, proc: &stratum_core::Proc) -> bool {
    match p {
        "hidden" => emits(proc, &hidden()),
        "pub" => emits(proc, &pub_()),
        _ => false,
    }
}

#[test]
fn agent_cannot_know_what_it_cannot_observe() {
    let lts = Lts::explore(&system(), 100);
    assert_eq!(
        lts.num_states(),
        3,
        "initial + two indistinguishable outcomes"
    );
    let ag = agents(&lts);

    // The state where the secret is actually out.
    let sb = (0..lts.num_states())
        .find(|&i| emits(lts.state(i), &hidden()))
        .expect("some state emits hidden");

    let phi = check(&lts, &prop("hidden"), &label);
    assert!(phi[sb], "hidden really does hold at that state");

    let knows_a = check_epistemic(&lts, &knows("A", prop("hidden")), &label, &ag);
    let knows_b = check_epistemic(&lts, &knows("B", prop("hidden")), &label, &ag);
    let poss_a = check_epistemic(&lts, &possible("A", prop("hidden")), &label, &ag);

    // A cannot distinguish the two outcomes, so it does not *know* the secret
    // even where it holds — but it does consider it possible.
    assert!(!knows_a[sb], "A must not know hidden");
    assert!(poss_a[sb], "A considers hidden possible");

    // B observes `hidden`, so it knows exactly when hidden holds.
    assert!(knows_b[sb], "B knows hidden");
}

#[test]
fn knowledge_is_truthful_and_omniscience_collapses() {
    let lts = Lts::explore(&system(), 100);
    let ag = agents(&lts);
    let phi = check(&lts, &prop("hidden"), &label);

    let knows_a = check_epistemic(&lts, &knows("A", prop("hidden")), &label, &ag);
    let knows_b = check_epistemic(&lts, &knows("B", prop("hidden")), &label, &ag);

    // Truthfulness (S5 reflexivity): K_A φ implies φ, at every state.
    for i in 0..lts.num_states() {
        assert!(!knows_a[i] || phi[i], "K_A φ must imply φ at state {i}");
    }

    // B's field is discrete w.r.t. `hidden`, so K_B φ collapses to φ exactly.
    assert_eq!(knows_b, phi, "an omniscient agent knows exactly the truth");
}

#[test]
fn undeclared_agent_is_omniscient() {
    // With no agents map, `K_Z φ` falls back to `φ` (discrete field default).
    let lts = Lts::explore(&system(), 100);
    let phi = check(&lts, &prop("hidden"), &label);
    let knows_z = check_epistemic(&lts, &knows("Z", prop("hidden")), &label, &Agents::new());
    assert_eq!(knows_z, phi);
}
