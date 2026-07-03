//! Tests for the labelled operational semantics ([`stratum_core::labelled`]).
//!
//! The headline acceptance criterion is **`τ` matches `Comm`**: the set of
//! `τ`-labelled transitions must equal the set of `step_labeled` reductions,
//! over many processes including random ones. The remaining tests pin the
//! visible actions (output free-only, late input, structural/par interleaving).

use std::collections::BTreeSet;

use stratum_core::congruence::canonicalize;
use stratum_core::labelled::{
    canonical_tau_transitions, canonical_transitions, tau_transitions, transitions, Action,
    Transition,
};
use stratum_core::reduce::step_labeled;
use stratum_core::term::{drop_, input, lift, output, par, quote, zero, Name, Proc};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// A genuinely `≡N`-distinct channel per `k`: the quote of `k` nested lifts.
/// Using lifts (not drops) avoids the quote-drop law `⌜*x⌝ ≡N x` collapsing
/// different `k` to the same name, so `chan(i) ≢N chan(j)` for `i ≠ j`.
fn chan(k: u64) -> Name {
    let mut p = zero();
    for _ in 0..k {
        p = lift(quote(zero()), p);
    }
    quote(p)
}

/// The `τ` transitions of `p` as a canonical, order-independent set:
/// `(canonical channel, canonical message, canonical reduct)`.
fn tau_set(p: &Proc) -> BTreeSet<(Name, Name, Proc)> {
    tau_transitions(p)
        .into_iter()
        .map(|t| match t {
            Transition::Tau {
                channel,
                message,
                reduct,
            } => (channel, message, canonicalize(&reduct)),
            _ => unreachable!("tau_transitions yields only Tau"),
        })
        .collect()
}

/// The `Comm` steps of `p` (`step_labeled`) in the same canonical set shape.
fn comm_set(p: &Proc) -> BTreeSet<(Name, Name, Proc)> {
    step_labeled(p)
        .into_iter()
        .map(|s| (s.channel, s.message, canonicalize(&s.reduct)))
        .collect()
}

// ---------------------------------------------------------------------------
// Output actions — free output, never bound (no ν in the ρ-calculus).
// ---------------------------------------------------------------------------

#[test]
fn bare_output_has_exactly_the_output_transition_to_zero() {
    // x⟨|0|⟩ --x!⌜0⌝--> 0
    let x = chan(0);
    let p = lift(x.clone(), zero());
    let ts = transitions(&p);
    assert_eq!(ts.len(), 1, "a bare lift has exactly one transition");
    match &ts[0] {
        Transition::Out {
            chan,
            msg,
            residual,
        } => {
            assert!(stratum_core::name_equiv(chan, &x));
            assert_eq!(*msg, stratum_core::canonicalize_name(&quote(zero())));
            assert_eq!(
                canonicalize(residual),
                Proc::Zero,
                "residual of a bare lift is 0"
            );
        }
        other => panic!("expected an output transition, got {other:?}"),
    }
}

#[test]
fn output_is_free_never_bound() {
    // The message emitted is a plain, already-formed name ⌜Q⌝ — there is no
    // bound output / scope extrusion because the calculus has no ν. We witness
    // this by checking the message is exactly the reified lifted body, carrying
    // no fresh binder, and that the action exposes it as a Name.
    let x = chan(1);
    let q = lift(chan(2), zero()); // a non-trivial payload Q
    let p = lift(x.clone(), q.clone());
    let ts = transitions(&p);
    let Transition::Out { msg, .. } = &ts[0] else {
        panic!("expected output");
    };
    // The message is ⌜Q⌝ verbatim (canonical), a free name.
    assert_eq!(*msg, stratum_core::canonicalize_name(&quote(q)));
    // Action mirrors it.
    match ts[0].action() {
        Action::Out(c, m) => {
            assert!(stratum_core::name_equiv(&c, &x));
            assert_eq!(m, *msg);
        }
        other => panic!("expected Out action, got {other:?}"),
    }
}

#[test]
fn composite_emits_each_of_its_outputs() {
    // x⟨|0|⟩ | y⟨|0|⟩ has two output transitions, each leaving the other behind.
    let x = chan(0);
    let y = chan(1);
    let p = par([lift(x.clone(), zero()), lift(y.clone(), zero())]);
    let outs: Vec<_> = transitions(&p)
        .into_iter()
        .filter(|t| matches!(t, Transition::Out { .. }))
        .collect();
    assert_eq!(outs.len(), 2);
    // The x-output leaves y⟨|0|⟩ behind, and vice versa.
    for t in &outs {
        let Transition::Out { chan, residual, .. } = t else {
            unreachable!()
        };
        if stratum_core::name_equiv(chan, &x) {
            assert_eq!(
                canonicalize(residual),
                canonicalize(&lift(y.clone(), zero()))
            );
        } else {
            assert!(stratum_core::name_equiv(chan, &y));
            assert_eq!(
                canonicalize(residual),
                canonicalize(&lift(x.clone(), zero()))
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Input actions — late / symbolic style.
// ---------------------------------------------------------------------------

#[test]
fn late_input_yields_an_abstraction_and_binds_correctly() {
    // x(y).*y --x?--> (y)*y. Instantiating with ⌜R⌝ must run R (semantic subst).
    let x = chan(0);
    let p = input(x.clone(), drop_);
    let ts = transitions(&p);
    let ins: Vec<_> = ts
        .iter()
        .filter(|t| matches!(t, Transition::In { .. }))
        .collect();
    assert_eq!(ins.len(), 1, "one late input transition");
    let Transition::In { chan: c, abs } = ins[0] else {
        unreachable!()
    };
    assert!(stratum_core::name_equiv(c, &x));

    // Instantiate with a received name ⌜R⌝ where R = z⟨|0|⟩.
    let r = lift(chan(3), zero());
    let received = quote(r.clone());
    let got = abs.instantiate(&received);
    // (y)*y applied to ⌜R⌝ runs R (drop of the substituted quote, §2.7).
    assert_eq!(canonicalize(&got), canonicalize(&r));
}

#[test]
fn input_is_finitely_branching() {
    // The whole point of late style: exactly one input transition regardless of
    // the infinitely many names that could be received.
    let x = chan(0);
    let p = input(x, |y| par([drop_(y.clone()), drop_(y)]));
    let ins = transitions(&p)
        .into_iter()
        .filter(|t| matches!(t, Transition::In { .. }))
        .count();
    assert_eq!(ins, 1);
}

// ---------------------------------------------------------------------------
// Structural / par: a matching output and input in parallel yield τ = Comm.
// ---------------------------------------------------------------------------

#[test]
fn output_and_matching_input_in_parallel_yield_tau_matching_comm() {
    // x⟨|Q|⟩ | x(y).*y  --τ-->  Q
    let x = chan(0);
    let q = lift(chan(2), zero());
    let sys = par([lift(x.clone(), q.clone()), input(x.clone(), drop_)]);

    let taus = tau_transitions(&sys);
    assert_eq!(taus.len(), 1, "exactly one synchronization");
    let Transition::Tau { reduct, .. } = &taus[0] else {
        unreachable!()
    };
    // Reduct is Q (dropping the received ⌜Q⌝ runs Q).
    assert_eq!(canonicalize(reduct), canonicalize(&q));

    // And it coincides with Comm exactly.
    assert_eq!(tau_set(&sys), comm_set(&sys));
}

#[test]
fn non_matching_channels_do_not_synchronize() {
    // Different channels ⇒ no τ, but each still offers its visible action.
    let sys = par([lift(chan(0), zero()), input(chan(1), |_| zero())]);
    assert!(tau_transitions(&sys).is_empty());
    let kinds: Vec<Action> = transitions(&sys).iter().map(Transition::action).collect();
    assert!(kinds.iter().any(|a| matches!(a, Action::Out(..))));
    assert!(kinds.iter().any(|a| matches!(a, Action::In(..))));
}

#[test]
fn actions_interleave_through_parallel() {
    // (x⟨|0|⟩ | x(y).0) | z⟨|0|⟩ : the τ carries z⟨|0|⟩ along, and z still emits.
    let x = chan(0);
    let z = chan(5);
    let sys = par([
        lift(x.clone(), zero()),
        input(x.clone(), |_| zero()),
        lift(z.clone(), zero()),
    ]);
    // τ reduct still has the untouched z output.
    let Transition::Tau { reduct, .. } = &tau_transitions(&sys)[0] else {
        panic!("expected a τ");
    };
    assert_eq!(canonicalize(reduct), canonicalize(&lift(z.clone(), zero())));
    // z's output is available as a visible action of the composite.
    assert!(transitions(&sys).iter().any(|t| matches!(
        t,
        Transition::Out { chan, .. } if stratum_core::name_equiv(chan, &z)
    )));
    // τ still matches Comm on this composite.
    assert_eq!(tau_set(&sys), comm_set(&sys));
}

// ---------------------------------------------------------------------------
// Headline: τ matches Comm over many processes, including random ones.
// ---------------------------------------------------------------------------

/// Minimal deterministic xorshift64 PRNG — no deps, no wall-clock.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng((seed ^ 0x9E37_79B9_7F4A_7C15) | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A small random closed process built from a fixed pool of channels, so that
/// synchronizations actually occur with reasonable frequency.
fn random_proc(rng: &mut Rng, depth: usize) -> Proc {
    // Channel pool with real ≡N-collisions so Comm fires.
    let pool = [chan(0), chan(1), chan(2)];
    if depth == 0 {
        return match rng.below(4) {
            0 => zero(),
            1 => lift(pool[rng.below(pool.len())].clone(), zero()),
            2 => drop_(pool[rng.below(pool.len())].clone()),
            _ => input(pool[rng.below(pool.len())].clone(), |_| zero()),
        };
    }
    match rng.below(6) {
        0 => zero(),
        1 => {
            let c = pool[rng.below(pool.len())].clone();
            let a = random_proc(rng, depth - 1);
            lift(c, a)
        }
        2 => {
            let c = pool[rng.below(pool.len())].clone();
            // Body may drop the bound name (exercises semantic subst on τ).
            if rng.below(2) == 0 {
                input(c, drop_)
            } else {
                let b = random_proc(rng, depth - 1);
                input(c, move |_| b)
            }
        }
        3 => drop_(pool[rng.below(pool.len())].clone()),
        4 => {
            // Output sugar x[y] = x⟨|*y|⟩ — reflective payload path.
            let c = pool[rng.below(pool.len())].clone();
            let m = pool[rng.below(pool.len())].clone();
            output(c, m)
        }
        _ => {
            let n = 1 + rng.below(3);
            par((0..n).map(|_| random_proc(rng, depth - 1)))
        }
    }
}

#[test]
fn tau_matches_comm_on_fixed_processes() {
    let x = chan(0);
    let y = chan(1);
    let cases = [
        zero(),
        lift(x.clone(), zero()),
        input(x.clone(), |_| zero()),
        // single Comm
        par([lift(x.clone(), zero()), input(x.clone(), drop_)]),
        // two receivers, one sender: two distinct Comm redexes
        par([
            lift(x.clone(), zero()),
            input(x.clone(), |_| zero()),
            input(x.clone(), drop_),
        ]),
        // two senders, one receiver
        par([
            lift(x.clone(), zero()),
            lift(x.clone(), lift(y.clone(), zero())),
            input(x.clone(), drop_),
        ]),
        // no match
        par([lift(x.clone(), zero()), input(y.clone(), |_| zero())]),
        // cross pair on two channels
        par([
            lift(x.clone(), zero()),
            input(x.clone(), |_| zero()),
            lift(y.clone(), zero()),
            input(y.clone(), drop_),
        ]),
        // quote-drop channel match: ⌜0⌝ vs ⌜*⌜0⌝⌝ are ≡N-EQUAL (⌜*x⌝ ≡N x, §2.4)
        // but syntactically DISTINCT. The lift fires with the input despite the
        // channels not being identical, exercising the interesting part of the
        // name_equiv guard — τ must still equal Comm here.
        par([
            lift(quote(zero()), zero()),
            input(quote(drop_(quote(zero()))), drop_),
        ]),
    ];
    for (i, p) in cases.iter().enumerate() {
        assert_eq!(tau_set(p), comm_set(p), "τ ≠ Comm on fixed case {i}: {p:?}");
    }
}

/// The quote-drop channel case in isolation: a lift on `⌜0⌝` and an input on
/// the `≡N`-equal but syntactically different `⌜*⌜0⌝⌝` DO synchronize, and τ
/// coincides with Comm. This pins the non-trivial `name_equiv` guard that the
/// `chan(k)` pool (all syntactically canonical) never reaches.
#[test]
fn tau_matches_comm_on_quote_drop_channel_match() {
    let sender_chan = quote(zero()); // ⌜0⌝
    let receiver_chan = quote(drop_(quote(zero()))); // ⌜*⌜0⌝⌝ ≡N ⌜0⌝
                                                     // Sanity: the two channels are ≡N-equal yet syntactically distinct.
    assert!(stratum_core::name_equiv(&sender_chan, &receiver_chan));
    assert_ne!(sender_chan, receiver_chan);

    let sys = par([
        lift(sender_chan, lift(chan(2), zero())),
        input(receiver_chan, drop_),
    ]);
    // A τ actually fires (the guard is not vacuously false).
    assert_eq!(tau_transitions(&sys).len(), 1);
    // And it matches Comm exactly.
    assert_eq!(tau_set(&sys), comm_set(&sys));
}

#[test]
fn canonical_transitions_dedup_duplicate_components_like_step_labeled() {
    let x = chan(0);
    // Two ≡-identical senders and two ≡-identical receivers: the raw relation
    // has duplicate output/input edges and duplicate τ edges; the canonical
    // accessor collapses them exactly as step_labeled does.
    let sys = par([
        lift(x.clone(), zero()),
        lift(x.clone(), zero()),
        input(x.clone(), drop_),
        input(x.clone(), drop_),
    ]);

    // Raw: duplicated edges present.
    let raw = transitions(&sys);
    let raw_out = raw
        .iter()
        .filter(|t| matches!(t, Transition::Out { .. }))
        .count();
    let raw_in = raw
        .iter()
        .filter(|t| matches!(t, Transition::In { .. }))
        .count();
    assert_eq!(raw_out, 2, "two identical outputs appear twice raw");
    assert_eq!(raw_in, 2, "two identical inputs appear twice raw");

    // Canonical: one output edge, one input edge.
    let canon = canonical_transitions(&sys);
    let c_out = canon
        .iter()
        .filter(|t| matches!(t, Transition::Out { .. }))
        .count();
    let c_in = canon
        .iter()
        .filter(|t| matches!(t, Transition::In { .. }))
        .count();
    assert_eq!(c_out, 1, "identical outputs collapse to one canonical edge");
    assert_eq!(c_in, 1, "identical inputs collapse to one canonical edge");

    // The canonical τ fragment equals step_labeled's deduplicated step set.
    let canon_tau: BTreeSet<(Name, Name, Proc)> = canonical_tau_transitions(&sys)
        .into_iter()
        .map(|t| match t {
            Transition::Tau {
                channel,
                message,
                reduct,
            } => (channel, message, canonicalize(&reduct)),
            _ => unreachable!(),
        })
        .collect();
    assert_eq!(canon_tau, comm_set(&sys));
    // And it has exactly step_labeled's cardinality (no duplicate τ edges).
    assert_eq!(
        canonical_tau_transitions(&sys).len(),
        step_labeled(&sys).len()
    );
}

/// A random *system*: a top-level parallel of 2..=6 small agents over a shared
/// two-channel pool, so `Comm` synchronizations occur frequently (reduction is
/// shallow — only top-level components can fire). Exercises the full labelled
/// relation, not just τ-free fragments.
fn random_system(rng: &mut Rng) -> Proc {
    let n = 2 + rng.below(5); // 2..=6 agents
    par((0..n).map(|_| random_proc(rng, 2)))
}

#[test]
fn tau_matches_comm_on_random_processes() {
    let mut checked = 0usize;
    let mut with_tau = 0usize;
    for seed in 0..2000u64 {
        let mut rng = Rng::new(seed);
        let p = random_system(&mut rng);
        let taus = tau_set(&p);
        assert_eq!(taus, comm_set(&p), "τ ≠ Comm on random seed {seed}: {p:?}");
        if !taus.is_empty() {
            with_tau += 1;
        }
        checked += 1;
    }
    // Sanity: the generator actually produced synchronizing systems, so the
    // equality is not vacuously over τ-free processes only.
    assert_eq!(checked, 2000);
    assert!(
        with_tau > 100,
        "expected many random processes to have τ transitions, got {with_tau}"
    );
}

#[test]
fn every_tau_reduct_is_reachable_by_reduction_and_vice_versa() {
    // Cross-check the whole-process view: the τ residuals equal step's reducts.
    let x = chan(0);
    let sys = par([
        lift(x.clone(), zero()),
        input(x.clone(), drop_),
        input(x.clone(), |_| zero()),
    ]);
    let tau_reducts: BTreeSet<Proc> = tau_transitions(&sys)
        .into_iter()
        .map(|t| match t {
            Transition::Tau { reduct, .. } => canonicalize(&reduct),
            _ => unreachable!(),
        })
        .collect();
    let step_reducts: BTreeSet<Proc> = stratum_core::reduce::step(&sys)
        .iter()
        .map(canonicalize)
        .collect();
    assert_eq!(tau_reducts, step_reducts);
}
