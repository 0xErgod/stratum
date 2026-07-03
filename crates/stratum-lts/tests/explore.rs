//! Tests for LTS construction over ρ-calculus reduction.

use stratum_core::term::{drop_, input, lift, output, par, quote, zero};
use stratum_core::{canonicalize, canonicalize_name};
use stratum_lts::Lts;

/// `a⟨|0|⟩ | a(y).0` has exactly two states (initial, then `0`) and one edge,
/// labelled by the firing channel `@0`.
#[test]
fn single_comm() {
    let a = quote(zero());
    let sys = par([lift(a.clone(), zero()), input(a.clone(), |_| zero())]);
    let lts = Lts::explore(&sys, 100);

    assert_eq!(lts.num_states(), 2);
    assert_eq!(lts.num_transitions(), 1);
    assert!(!lts.is_truncated());

    let init = lts.initial();
    let edges = lts.transitions(init);
    assert_eq!(edges.len(), 1);
    assert_eq!(edges[0].label, canonicalize_name(&a));

    // The target is the normal form 0.
    let target = edges[0].target;
    assert_eq!(*lts.state(target), canonicalize(&zero()));
    assert!(lts.is_terminal(target));
}

/// A confluent diamond: two independent Comms on distinct channels can fire in
/// either order, meeting at a common normal form. Four states, four edges.
#[test]
fn confluent_diamond() {
    let a = quote(zero());
    let b = quote(lift(quote(zero()), zero())); // a distinct channel ⌜@0!(0)⌝
    let sys = par([
        lift(a.clone(), zero()),
        input(a, |_| zero()),
        lift(b.clone(), zero()),
        input(b, |_| zero()),
    ]);
    let lts = Lts::explore(&sys, 100);

    assert_eq!(lts.num_states(), 4, "initial, two intermediates, final");
    assert_eq!(lts.num_transitions(), 4, "two ways around the diamond");
    assert_eq!(lts.transitions(lts.initial()).len(), 2);

    // Exactly one terminal state (the common normal form).
    let terminals = (0..lts.num_states())
        .filter(|&i| lts.is_terminal(i))
        .count();
    assert_eq!(terminals, 1);
}

/// A term with no matching send/receive is a one-state, edgeless LTS.
#[test]
fn stuck_system() {
    let sender = lift(quote(zero()), zero());
    let receiver = input(quote(lift(quote(zero()), zero())), |_| zero());
    let lts = Lts::explore(&par([sender, receiver]), 100);

    assert_eq!(lts.num_states(), 1);
    assert_eq!(lts.num_transitions(), 0);
    assert!(lts.is_terminal(lts.initial()));
}

/// Replication has an infinite state space; exploration respects the bound and
/// reports truncation.
#[test]
fn replication_is_truncated() {
    fn replicator(x: stratum_core::Name) -> stratum_core::Proc {
        input(x.clone(), move |y| {
            par([output(x.clone(), y.clone()), drop_(y)])
        })
    }
    let x = quote(zero());
    let p = lift(quote(drop_(quote(zero()))), zero());
    let bang = par([
        lift(x.clone(), par([replicator(x.clone()), p])),
        replicator(x),
    ]);

    let lts = Lts::explore(&bang, 5);
    assert!(lts.num_states() <= 5);
    assert!(lts.is_truncated());
    // Every recorded transition points at a real state.
    for i in 0..lts.num_states() {
        for t in lts.transitions(i) {
            assert!(t.target < lts.num_states());
        }
    }
}

/// The DOT export mentions the initial node and is non-empty.
#[test]
fn dot_export() {
    let a = quote(zero());
    let sys = par([lift(a.clone(), zero()), input(a, |_| zero())]);
    let dot = Lts::explore(&sys, 100).to_dot();
    assert!(dot.starts_with("digraph lts {"));
    assert!(dot.contains("n0"));
    assert!(dot.trim_end().ends_with('}'));
}
