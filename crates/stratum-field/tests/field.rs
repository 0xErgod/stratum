//! Tests for the field grain: partition lattice laws, projections, and
//! measurability.

use stratum_core::term::{input, lift, par, quote, zero};
use stratum_core::Name;
use stratum_field::{generated_field, is_measurable, observational_field, project, Agent, Field};
use stratum_lts::Lts;

fn x() -> Name {
    quote(zero()) // observable channel @0
}
fn a() -> Name {
    quote(lift(quote(zero()), zero())) // internal channel @(@0!(0))
}

/// `a⟨|0|⟩ | a(y).x⟨|0|⟩` — two states: before and after the internal step, the
/// latter emitting on `x`.
fn system() -> stratum_core::Proc {
    par([lift(a(), zero()), input(a(), move |_| lift(x(), zero()))])
}

// -- partition lattice laws ------------------------------------------------

#[test]
fn refinement_is_a_partial_order() {
    let d = Field::discrete(4);
    let t = Field::trivial(4);
    let mid = Field::from_signatures(&[0, 0, 1, 1]);

    // reflexive
    assert!(mid.refines(&mid));
    // discrete is the bottom (finest), trivial the top (coarsest)
    assert!(d.refines(&mid) && mid.refines(&t));
    assert!(d.refines(&t));
    assert!(!t.refines(&d));
    // antisymmetry: mutual refinement ⇒ equal partition
    let mid2 = Field::from_signatures(&[9, 9, 5, 5]); // same partition, different labels
    assert!(mid.refines(&mid2) && mid2.refines(&mid));
    assert_eq!(mid, mid2);
}

#[test]
fn pooled_is_finer_common_knowledge_is_coarser() {
    let f = Field::from_signatures(&[0, 0, 1, 1]); // {01}{23}
    let g = Field::from_signatures(&[0, 1, 0, 1]); // {02}{13}

    let pooled = f.pooled(&g);
    let common = f.common_knowledge(&g);

    // pooled refines both inputs
    assert!(pooled.refines(&f) && pooled.refines(&g));
    // both inputs refine common knowledge
    assert!(f.refines(&common) && g.refines(&common));

    // here pooled is fully discrete and common knowledge fully trivial
    assert_eq!(pooled, Field::discrete(4));
    assert_eq!(common, Field::trivial(4));
}

// -- projections tie fields to observation ---------------------------------

#[test]
fn observation_and_projection() {
    let lts = Lts::explore(&system(), 100);
    assert_eq!(lts.num_states(), 2);

    // Find which state emits on x.
    let emitting: Vec<bool> = (0..lts.num_states())
        .map(|i| !project(lts.state(i), &[x()]).is_empty())
        .collect();
    assert_eq!(emitting.iter().filter(|b| **b).count(), 1);

    // Observing x separates the two states; observing nothing does not.
    let watch_x = observational_field(&lts, &[x()]);
    let watch_none = observational_field(&lts, &[]);
    assert_eq!(watch_x.num_atoms(), 2);
    assert_eq!(watch_none.num_atoms(), 1);
    // More observation ⇒ finer field (§F7).
    assert!(watch_x.refines(&watch_none));
}

#[test]
fn agent_field_via_obs() {
    let lts = Lts::explore(&system(), 100);
    let seer = Agent::observer(vec![x()]);
    let blind = Agent::observer(vec![]);
    assert_eq!(seer.field(&lts).num_atoms(), 2);
    assert_eq!(blind.field(&lts).num_atoms(), 1);
    assert!(seer.field(&lts).refines(&blind.field(&lts)));
}

// -- measurability = legible action ----------------------------------------

#[test]
fn measurability_matches_refinement_law() {
    // Action: "emits on x", one bool per state.
    let lts = Lts::explore(&system(), 100);
    let values: Vec<bool> = (0..lts.num_states())
        .map(|i| !project(lts.state(i), &[x()]).is_empty())
        .collect();

    let seer = observational_field(&lts, &[x()]);
    let blind = observational_field(&lts, &[]);

    // An agent that watches x can measure the action; a blind one cannot.
    assert!(is_measurable(&seer, &values));
    assert!(!is_measurable(&blind, &values));

    // The general law: measurable(F, act) ⟺ F refines the action's own field.
    let action_field = generated_field(&values);
    assert_eq!(is_measurable(&seer, &values), seer.refines(&action_field));
    assert_eq!(is_measurable(&blind, &values), blind.refines(&action_field));
}

#[test]
fn discrete_measures_everything_trivial_only_constants() {
    let vals = [1u8, 2, 2, 3];
    assert!(is_measurable(&Field::discrete(4), &vals));
    assert!(!is_measurable(&Field::trivial(4), &vals));

    let constant = [7u8, 7, 7, 7];
    assert!(is_measurable(&Field::trivial(4), &constant));
}
