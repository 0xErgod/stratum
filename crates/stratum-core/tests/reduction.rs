//! Reduction (§2.8) and closedness/congruence assurance tests.
//!
//! The golden reduction tests reproduce calculations Meredith & Radestock give
//! explicitly, so a passing suite is direct evidence of faithfulness.

use proptest::prelude::*;
use stratum_core::congruence::{canonicalize, name_equiv, structurally_congruent};
use stratum_core::reduce::{is_normal_form, reachable, step};
use stratum_core::term::{drop_, input, lift, output, par, quote, zero, Name, Proc};

/// Generator for closed processes whose names are quotes or in-scope bound
/// occurrences. Channels are mostly `⌜0⌝`, so `Comm` redexes arise naturally.
fn arb_proc() -> impl Strategy<Value = Proc> {
    let leaf = prop_oneof![
        Just(zero()),
        Just(drop_(quote(zero()))),
        Just(output(quote(zero()), quote(zero()))),
        Just(lift(quote(zero()), zero())),
    ];
    leaf.prop_recursive(4, 48, 4, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 2..4).prop_map(par),
            inner.clone().prop_map(|p| lift(quote(zero()), p)),
            (inner.clone(), any::<bool>()).prop_map(|(p, use_bound)| {
                input(quote(zero()), move |y| {
                    if use_bound {
                        par([drop_(y), p.clone()])
                    } else {
                        p.clone()
                    }
                })
            }),
        ]
    })
}

/// Count top-level parallel components of a *canonical* state equal to a given
/// canonical target.
fn count_components(state: &Proc, target: &Proc) -> usize {
    match state {
        Proc::Par(items) => items.iter().filter(|c| *c == target).count(),
        other => usize::from(other == target),
    }
}

/// §2.8 sugar justification: `x[z] | x(y).*y  →  *z`.
///
/// With `x = z = ⌜0⌝`, the receiver binds `y` to `⌜*⌜0⌝⌝ ≡N ⌜0⌝`, and running
/// `*y` yields `*⌜0⌝`.
#[test]
fn comm_sugar_step() {
    let x = quote(zero());
    let z = quote(zero());
    let sender = output(x.clone(), z); // x[z] = x⟨|*z|⟩
    let receiver = input(x, drop_); // x(y).*y

    let reducts = step(&par([sender, receiver]));
    assert_eq!(reducts.len(), 1, "exactly one Comm redex");

    let expected = canonicalize(&drop_(quote(zero()))); // *⌜0⌝
    assert_eq!(canonicalize(&reducts[0]), expected);
}

/// A single sender facing two distinct receivers has two distinct reducts —
/// reduction is genuinely nondeterministic (the branching the trace LTS needs).
#[test]
fn comm_is_nondeterministic() {
    let a = quote(zero());
    let mark1 = quote(drop_(quote(zero())));
    let mark2 = quote(output(quote(zero()), quote(zero())));
    let q1 = lift(mark1, zero());
    let q2 = lift(mark2, zero());

    let sender = lift(a.clone(), zero()); // a⟨|0|⟩
    let r1 = input(a.clone(), {
        let q1 = q1.clone();
        move |_| q1.clone()
    });
    let r2 = input(a, {
        let q2 = q2.clone();
        move |_| q2.clone()
    });

    let reducts = step(&par([sender, r1, r2]));
    assert_eq!(reducts.len(), 2, "one redex per receiver");

    let mut canon: Vec<Proc> = reducts.iter().map(canonicalize).collect();
    canon.sort();
    canon.dedup();
    assert_eq!(canon.len(), 2, "the two reducts are distinct");
}

/// §3 replication: `!P ≜ x⟨|D(x)|P|⟩ | D(x)` with `D(x) ≜ x(y).(x[y]|*y)`
/// unfolds, emitting a fresh standalone copy of `P` at every step while
/// regenerating the replicator. Reaching a state with two copies of `P` shows
/// the derived replication really replicates — no primitive `!` needed.
#[test]
fn replication_unfolds() {
    /// `D(x) = x(y).(x[y] | *y)`
    fn replicator(x: Name) -> Proc {
        input(x.clone(), move |y| {
            par([output(x.clone(), y.clone()), drop_(y)])
        })
    }
    /// `!P(x) = x⟨|D(x)|P|⟩ | D(x)`
    fn bang(x: Name, p: Proc) -> Proc {
        let inner = par([replicator(x.clone()), p]);
        par([lift(x.clone(), inner), replicator(x)])
    }

    let x = quote(zero());
    // P is a lift on a channel distinct from x, so standalone copies are
    // recognizable and never confused with the regenerated sender on x.
    let p = lift(quote(drop_(quote(zero()))), zero());
    let canon_p = canonicalize(&p);

    let states = reachable(&bang(x, p.clone()), 3);
    let max_copies = states
        .iter()
        .map(|s| count_components(s, &canon_p))
        .max()
        .unwrap_or(0);

    assert!(
        max_copies >= 2,
        "replication should produce at least two copies of P (saw {max_copies})",
    );
}

/// A term with no matching send/receive pair is in normal form.
#[test]
fn stuck_terms_are_normal() {
    // Genuinely distinct channels ⌜0⌝ vs ⌜⌜0⌝⟨|0|⟩⌝: not ≡N (the latter is a
    // quoted *lift*, not a quoted drop, so quote-drop does not collapse it), so
    // no Comm is possible.
    let other_chan = quote(lift(quote(zero()), zero()));
    assert!(!name_equiv(&quote(zero()), &other_chan));
    let sender = lift(quote(zero()), zero());
    let receiver = input(other_chan, |_| zero());
    assert!(is_normal_form(&par([sender, receiver])));
    assert!(is_normal_form(&zero()));
}

proptest! {
    /// Reduction preserves closedness: stepping a closed term yields closed
    /// terms (§2.2 well-formedness invariant).
    #[test]
    fn step_preserves_closedness(p in arb_proc()) {
        prop_assert!(p.is_closed());
        for reduct in step(&p) {
            prop_assert!(reduct.is_closed(), "reduct escaped closedness");
        }
    }

    /// Generated terms are closed by construction.
    #[test]
    fn generated_terms_are_closed(p in arb_proc()) {
        prop_assert!(p.is_closed());
    }

    /// Structural congruence is a *congruence*: `P ≡ P'` is preserved by every
    /// term constructor. We use the genuine ≡-witness `P' = 0 | P`.
    #[test]
    fn congruence_under_all_contexts(a in arb_proc(), filler in arb_proc()) {
        let a2 = par([zero(), a.clone()]);
        prop_assert!(structurally_congruent(&a, &a2));

        // under parallel
        prop_assert!(structurally_congruent(
            &par([a.clone(), filler.clone()]),
            &par([a2.clone(), filler]),
        ));
        // under lift
        prop_assert!(structurally_congruent(
            &lift(quote(zero()), a.clone()),
            &lift(quote(zero()), a2.clone()),
        ));
        // under a quote (struct-equiv for ≡N, §2.4)
        prop_assert!(name_equiv(&quote(a.clone()), &quote(a2.clone())));
        // under an input prefix
        prop_assert!(structurally_congruent(
            &input(quote(zero()), |_| a.clone()),
            &input(quote(zero()), |_| a2.clone()),
        ));
    }
}
