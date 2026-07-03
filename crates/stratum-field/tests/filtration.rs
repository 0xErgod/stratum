//! Tests for time-as-filtration (SPEC §F11): `Ω` = runs, `F_t` = knowledge after
//! `t` steps, non-decreasing in information.

use stratum_core::term::{input, lift, par, quote, zero};
use stratum_core::{canonicalize_name, name_equiv, Name, Proc};
use stratum_field::filtration::{enumerate_traces, filtration, is_filtration};
use stratum_field::Field;
use stratum_lts::Lts;

/// Distinct internal channels `@(@0!(@0!…!0))` of increasing nesting depth — all
/// pairwise `≢N`, and never quotes-of-drops (see the crate's channel gotcha).
fn ch(n: usize) -> Name {
    let mut p = zero();
    for _ in 0..=n {
        p = lift(quote(zero()), p);
    }
    quote(p)
}

/// A system whose branch is observable only at the *last* step:
/// `go⟨|0|⟩ | go(x).( c⟨|0|⟩ | a⟨|0|⟩ | a(y).d⟨|0|⟩ | a(z).0 )`.
///
/// After `go` fires (step 1) every run shows a barb on `c` and nothing on `d`.
/// The internal `a` output then reacts with one of two inputs (step 2): one
/// branch emits on `d`, the other does not. So watching `{c, d}` the two runs are
/// indistinguishable until the second step is observed.
fn branch_system() -> Proc {
    let c = ch(0);
    let d = ch(1);
    let a = ch(2);
    let go = ch(3);
    let body = par([
        lift(c, zero()),
        lift(a.clone(), zero()),
        input(a.clone(), move |_| lift(d, zero())),
        input(a, |_| zero()),
    ]);
    par([lift(go.clone(), zero()), input(go, move |_| body)])
}

#[test]
fn traces_are_maximal_runs() {
    let lts = Lts::explore(&branch_system(), 100);
    // s0 --go--> s1 --a--> s2A ; s1 --a--> s2B
    assert_eq!(lts.num_states(), 4);
    let traces = enumerate_traces(&lts, 5);
    // Exactly two maximal runs, each ending at a terminal state after 2 steps.
    assert_eq!(traces.len(), 2);
    for tr in &traces {
        assert_eq!(tr.len(), 2);
        assert_eq!(tr.states.len(), 3);
        assert!(lts.is_terminal(*tr.states.last().unwrap()));
    }
}

#[test]
fn f0_is_trivial_and_sequence_is_a_filtration() {
    let lts = Lts::explore(&branch_system(), 100);
    let fields = filtration(&lts, &[ch(0), ch(1)], 4);
    // Ω's longest run visits 3 states, so the filtration is F_0 .. F_3 regardless
    // of the (larger) step budget — the finest field reveals the whole run.
    assert_eq!(fields.len(), 4); // F_0 .. F_3

    // F_0: no observations yet ⇒ one atom (the agent knows nothing).
    assert_eq!(fields[0].num_atoms(), 1);
    // Information is non-decreasing along time.
    assert!(is_filtration(&fields));
}

#[test]
fn a_late_distinction_makes_a_later_field_strictly_finer() {
    let lts = Lts::explore(&branch_system(), 100);
    let fields = filtration(&lts, &[ch(0), ch(1)], 3);

    // The two runs agree on the barb-on-c through step 2, so F_2 cannot separate
    // them; only the third visited state (the barb on d) tells them apart.
    assert_eq!(fields[2].num_atoms(), 1);
    assert_eq!(fields[3].num_atoms(), 2);
    // Strictly finer: F_3 refines F_2 but has more atoms.
    assert!(fields[3].refines(&fields[2]));
    assert!(fields[3].num_atoms() > fields[2].num_atoms());
}

#[test]
fn observing_more_channels_yields_a_pointwise_finer_filtration() {
    let lts = Lts::explore(&branch_system(), 100);
    let watch_cd = filtration(&lts, &[ch(0), ch(1)], 3);
    let watch_c = filtration(&lts, &[ch(0)], 3);

    assert_eq!(watch_cd.len(), watch_c.len());
    // Both are filtrations; watching more channels refines pointwise (§F7).
    assert!(is_filtration(&watch_cd) && is_filtration(&watch_c));
    for (fine, coarse) in watch_cd.iter().zip(watch_c.iter()) {
        assert!(fine.refines(coarse));
    }
    // Dropping d collapses the only distinction, so watching c alone never
    // separates the two runs.
    assert_eq!(watch_c.last().unwrap().num_atoms(), 1);
    assert_eq!(watch_cd.last().unwrap().num_atoms(), 2);
}

#[test]
fn is_filtration_rejects_a_coarsening_sequence() {
    // A sequence that *loses* information over time is not a filtration.
    let coarsening = [Field::discrete(2), Field::trivial(2)];
    assert!(!is_filtration(&coarsening));
    // The refining direction is accepted.
    let refining = [Field::trivial(2), Field::discrete(2)];
    assert!(is_filtration(&refining));
}

#[test]
fn horizon_separates_full_budget_runs() {
    // Regression: when a run uses the entire step budget, the finest field must
    // still reveal its last visited state (no off-by-one dropping the horizon).
    let lts = Lts::explore(&branch_system(), 100);
    // max_len == the run length (2): the two runs diverge only at the horizon.
    let fields = filtration(&lts, &[ch(0), ch(1)], 2);
    assert_eq!(fields.last().unwrap().num_atoms(), 2);
}

/// A trace reads as a sequence of `(channel, message)` events. On the
/// handshake-style `req⟨|0|⟩ | req(x).ack⟨|0|⟩` the sole run fires once: on `req`
/// (canonical `@0`) carrying the reified value `@0` (the quote of the sent `0`).
#[test]
fn trace_records_channel_message_pairs() {
    let req = quote(zero()); // firing channel @0
    let ack = ch(1); // a distinct reply channel nobody listens on
    let sys = par([
        lift(req.clone(), zero()),                              // req⟨|0|⟩
        input(req.clone(), move |_| lift(ack.clone(), zero())), // req(x).ack⟨|0|⟩
    ]);
    let lts = Lts::explore(&sys, 100);
    let traces = enumerate_traces(&lts, 5);

    // One maximal run: req fires, leaving the (stuck) ack emitter.
    assert_eq!(traces.len(), 1);
    let tr = &traces[0];
    assert_eq!(tr.len(), 1);
    assert_eq!(tr.labels.len(), tr.messages.len());

    // The first (only) event: channel req == @0, message == the reified 0 (@0).
    let expected_channel = canonicalize_name(&req); // @0
    let expected_message = canonicalize_name(&quote(zero())); // @0 = ⌜0⌝
    assert_eq!(tr.labels[0], expected_channel);
    assert_eq!(tr.messages[0], expected_message);

    // The trace is a sequence of (channel, message) pairs.
    let events: Vec<(Name, Name)> = tr
        .labels
        .iter()
        .cloned()
        .zip(tr.messages.iter().cloned())
        .collect();
    assert_eq!(events, vec![(expected_channel, expected_message)]);
}

#[test]
fn channels_are_distinct() {
    // Guard the fixture: the four channels must be pairwise ≢N.
    let chans: Vec<Name> = (0..4).map(ch).collect();
    for i in 0..chans.len() {
        for j in (i + 1)..chans.len() {
            assert!(!name_equiv(&chans[i], &chans[j]));
        }
    }
}
