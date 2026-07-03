//! Tests for payload-granularity content (SPEC §F3): payload separates barbs
//! that presence lumps together, and is always at least as fine as presence.

use stratum_core::term::{input, lift, quote, zero, par};
use stratum_core::Name;
use stratum_field::content::{payload_field, project_payload};
use stratum_field::{observational_field, project};
use stratum_lts::Lts;

fn c() -> Name {
    quote(zero()) // observed channel @0
}
fn a() -> Name {
    quote(lift(quote(zero()), zero())) // internal channel @(@0!(0))
}

/// `a⟨|0|⟩ | a(y).c⟨|0|⟩ | a(z).c⟨|@0!(0)|⟩` — the internal `a` output reacts with
/// one of two inputs, yielding two terminal states that both emit on `c` but with
/// *different* payloads (`0` vs `@0!(0)`).
fn system() -> stratum_core::Proc {
    par([
        lift(a(), zero()),
        input(a(), |_| lift(c(), zero())),
        input(a(), |_| lift(c(), lift(quote(zero()), zero()))),
    ])
}

#[test]
fn payload_separates_barbs_that_presence_merges() {
    let lts = Lts::explore(&system(), 100);
    let presence = observational_field(&lts, &[c()]);
    let payload = payload_field(&lts, &[c()]);

    // The two states that emit on c.
    let emitters: Vec<usize> = (0..lts.num_states())
        .filter(|&i| !project(lts.state(i), &[c()]).is_empty())
        .collect();
    assert_eq!(emitters.len(), 2);
    let (u, v) = (emitters[0], emitters[1]);

    // Presence lumps them together; payload tells them apart.
    assert_eq!(presence.atom_of(u), presence.atom_of(v));
    assert_ne!(payload.atom_of(u), payload.atom_of(v));

    // The emitters carry genuinely different payload multisets.
    assert_ne!(
        project_payload(lts.state(u), &[c()]),
        project_payload(lts.state(v), &[c()])
    );
}

#[test]
fn payload_is_at_least_as_fine_as_presence() {
    let lts = Lts::explore(&system(), 100);
    let presence = observational_field(&lts, &[c()]);
    let payload = payload_field(&lts, &[c()]);

    // Payload refines presence (§F7): its key set is exactly the presence set.
    assert!(payload.refines(&presence));
    // Strictly finer here: presence has 2 atoms, payload distinguishes 3.
    assert_eq!(presence.num_atoms(), 2);
    assert_eq!(payload.num_atoms(), 3);
}

#[test]
fn empty_observation_gives_empty_payload() {
    let lts = Lts::explore(&system(), 100);
    // With nothing observed, every state's payload projection is empty ⇒ trivial.
    for i in 0..lts.num_states() {
        assert!(project_payload(lts.state(i), &[]).is_empty());
    }
    assert_eq!(payload_field(&lts, &[]).num_atoms(), 1);
}
