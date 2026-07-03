//! Tests for partial-order reduction (`Lts::explore_por`).
//!
//! POR is an **opt-in, reduced** explorer that must agree with the full
//! [`Lts::explore`] on the *preserved* property class — reachability/safety of
//! barb-observations on the `observed` channels — while (often dramatically)
//! reducing the state count. It deliberately does **not** preserve bisimulation
//! or next-time modalities, so those are never asserted here.
//!
//! The suite has three parts:
//!   * unit tests pinning the independence and visibility behaviour;
//!   * a seeded **differential** test over many random concurrent ρ-systems,
//!     comparing reachable observed barbs and `EF`/`AG` barb verdicts (via the
//!     real `stratum-logic` checker) and asserting `por ≤ full` on state count;
//!   * an **acceptance benchmark** of N genuinely independent Comms, where full
//!     exploration is `2^N` states and POR is linear.

use std::collections::BTreeSet;

use stratum_core::term::{input, lift, par, zero};
use stratum_core::{canonicalize_name, Name, Proc};
use stratum_logic::examples::emits;
use stratum_logic::{ag, ef, holds, prop};
use stratum_lts::Lts;

/// A distinct closed channel per `k`: `⌜ k nested lifts ⌝`. `distinct_chan(0)`
/// is `⌜0⌝`; higher `k` are pairwise distinct and never `≡N ⌜0⌝`.
fn distinct_chan(k: usize) -> Name {
    let mut p = zero();
    for _ in 0..k {
        p = lift(Name::Quote(Box::new(zero())), p);
    }
    Name::Quote(Box::new(p))
}

/// The set of observed barbs reachable anywhere in `lts` (canonical channels).
fn reachable_barbs(lts: &Lts, observed: &[Name]) -> BTreeSet<Name> {
    let mut set = BTreeSet::new();
    for i in 0..lts.num_states() {
        for c in components(lts.state(i)) {
            if let Proc::Lift { chan, .. } = c {
                if observed.iter().any(|n| stratum_core::name_equiv(chan, n)) {
                    set.insert(canonicalize_name(chan));
                }
            }
        }
    }
    set
}

fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Zero => Vec::new(),
        Proc::Par(ps) => ps.iter().collect(),
        other => vec![other],
    }
}

/// A pair `a⟨|0|⟩ | a(y).0` that reacts once on channel `a`.
fn comm_pair(a: Name) -> Vec<Proc> {
    vec![lift(a.clone(), zero()), input(a, |_| zero())]
}

// ---------------------------------------------------------------------------
// Unit tests: independence and visibility.
// ---------------------------------------------------------------------------

/// Two independent Comms on distinct, *unobserved* channels: POR fires them in a
/// single order (a linear chain of 3 states) instead of the full 4-state
/// diamond, yet reaches the same (empty) observed barbs.
#[test]
fn independent_unobserved_is_reduced() {
    let a = distinct_chan(1);
    let b = distinct_chan(2);
    let mut comps = comm_pair(a);
    comps.extend(comm_pair(b));
    let sys = par(comps);

    let full = Lts::explore(&sys, 100);
    let por = Lts::explore_por(&sys, 100, &[]);

    assert_eq!(full.num_states(), 4, "diamond: init, two mids, final");
    assert_eq!(por.num_states(), 3, "POR linearizes the diamond");
    assert!(por.num_states() < full.num_states());
    assert!(!por.is_truncated());
    assert_eq!(reachable_barbs(&full, &[]), reachable_barbs(&por, &[]));
}

/// The *same* diamond, but now both channels are observed, so each Comm consumes
/// an observed barb and is therefore **visible**. POR must fall back to full
/// expansion (C2), reproducing all 4 states.
#[test]
fn visible_steps_are_not_reduced() {
    let a = distinct_chan(1);
    let b = distinct_chan(2);
    let mut comps = comm_pair(a.clone());
    comps.extend(comm_pair(b.clone()));
    let sys = par(comps);

    let full = Lts::explore(&sys, 100);
    let por = Lts::explore_por(&sys, 100, &[a, b]);

    assert_eq!(full.num_states(), 4);
    assert_eq!(por.num_states(), 4, "all steps visible ⇒ no reduction (C2)");
}

/// A component using a *bound variable in a channel position*
/// (`c(y).(y(z).0)`) makes future-stability fail: firing `c` could surface a
/// fresh channel, so POR conservatively declines to defer and expands fully —
/// never producing a wrong (over-reduced) result.
#[test]
fn var_channel_forces_full_expansion() {
    let a = distinct_chan(1);
    let c = distinct_chan(2);
    // c(y).(y(z).0): a receiver whose continuation inputs on the received name.
    let tricky = input(c.clone(), |y| input(y, |_| zero()));
    let mut comps = comm_pair(a);
    comps.push(lift(c.clone(), zero()));
    comps.push(tricky);
    let sys = par(comps);

    let full = Lts::explore(&sys, 200);
    let por = Lts::explore_por(&sys, 200, &[]);

    // Whatever the exact counts, POR must agree with full on reachable barbs and
    // must never exceed its state count.
    assert!(por.num_states() <= full.num_states());
    assert_eq!(reachable_barbs(&full, &[]), reachable_barbs(&por, &[]));
}

// ---------------------------------------------------------------------------
// Differential test over random concurrent ρ-systems.
// ---------------------------------------------------------------------------

/// A tiny deterministic xorshift64 PRNG (no deps, no wall-clock).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        // Mix the seed, then force it odd so it is never the zero fixed point.
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

/// Build a random closed ρ-system from a small channel alphabet, mixing
/// independent and conflicting reactions plus occasional name-passing.
fn random_system(rng: &mut Rng, chans: &[Name]) -> Proc {
    let n = chans.len();
    let count = 2 + rng.below(6); // 2..=7 components
    let mut comps = Vec::new();
    for _ in 0..count {
        let c = chans[rng.below(n)].clone();
        match rng.below(4) {
            0 => comps.push(lift(c, zero())), // a bare output (possible barb)
            1 => comps.push(input(c, |_| zero())), // a plain receiver
            2 => {
                // receiver that emits on another channel (produces a new barb)
                let d = chans[rng.below(n)].clone();
                comps.push(input(c, move |_| lift(d, zero())));
            }
            _ => {
                // name-passing receiver: continuation uses the received name as a
                // channel — exercises the var-channel safety path.
                comps.push(input(c, |y| input(y, |_| zero())));
            }
        }
    }
    par(comps)
}

/// For every random system: the full and POR explorations must agree on the
/// preserved class — reachable observed barbs and per-channel `EF`/`AG` barb
/// verdicts — and POR must never have more states.
#[test]
fn differential_preserves_barb_reachability_and_safety() {
    let chans: Vec<Name> = (0..3).map(distinct_chan).collect();
    let bound = 400;
    let trials = 400;
    let mut compared = 0;
    let mut strictly_reduced = 0;

    for seed in 0..trials {
        let mut rng = Rng::new(seed as u64);
        let sys = random_system(&mut rng, &chans);

        // Observe a random non-empty subset of the alphabet.
        let mut observed = Vec::new();
        for c in &chans {
            if rng.below(2) == 0 {
                observed.push(c.clone());
            }
        }
        if observed.is_empty() {
            observed.push(chans[0].clone());
        }

        let full = Lts::explore(&sys, bound);
        let por = Lts::explore_por(&sys, bound, &observed);
        if full.is_truncated() || por.is_truncated() {
            continue; // cannot compare a truncated fragment
        }
        compared += 1;

        // (iii) POR never grows the state space.
        assert!(
            por.num_states() <= full.num_states(),
            "seed {seed}: POR {} > full {}",
            por.num_states(),
            full.num_states()
        );
        if por.num_states() < full.num_states() {
            strictly_reduced += 1;
        }

        // (i) identical set of reachable observed barbs.
        assert_eq!(
            reachable_barbs(&full, &observed),
            reachable_barbs(&por, &observed),
            "seed {seed}: reachable observed barbs differ"
        );

        // (ii) identical EF / AG barb verdicts, via the real μ-calculus checker.
        for (i, o) in observed.iter().enumerate() {
            let o = o.clone();
            let label = move |_name: &str, proc: &Proc| emits(proc, &o);
            let name = format!("b{i}");
            assert_eq!(
                holds(&full, &ef(prop(&name)), &label),
                holds(&por, &ef(prop(&name)), &label),
                "seed {seed}: EF(barb {i}) verdict differs"
            );
            assert_eq!(
                holds(&full, &ag(prop(&name)), &label),
                holds(&por, &ag(prop(&name)), &label),
                "seed {seed}: AG(barb {i}) verdict differs"
            );
        }
    }

    // The suite must actually exercise POR: many systems, and POR must strictly
    // reduce at least some of them.
    assert!(compared > 200, "too few comparable systems: {compared}");
    // The random generator is conflict- and name-passing-heavy on a 3-channel
    // alphabet, so only a handful of its systems are independent enough to
    // strictly reduce; that sanity floor stays, but the *meaningful* reduction
    // bar below is deterministic and robust to the generator.
    assert!(
        strictly_reduced > 0,
        "POR never reduced any random system — the fuzzer is vacuous"
    );

    // Deterministic guaranteed-reduction check: for a family of independent-heavy
    // systems of growing size, POR MUST strictly reduce — by an exponential
    // margin — while agreeing with the full LTS on the preserved class. Exact
    // counts (2^n vs n+1) are asserted, so this cannot silently degrade.
    for n in 2..=6usize {
        let mut comps = Vec::new();
        for k in 0..n {
            comps.extend(comm_pair(distinct_chan(k + 1))); // distinct channels
        }
        let sys = par(comps);

        let full = Lts::explore(&sys, 1 << 12);
        let por = Lts::explore_por(&sys, 1 << 12, &[]);
        assert!(!full.is_truncated() && !por.is_truncated());

        assert_eq!(full.num_states(), 1 << n, "n={n}: full is 2^n");
        assert_eq!(por.num_states(), n + 1, "n={n}: POR is linear");
        assert!(
            por.num_states() < full.num_states(),
            "n={n}: POR {} not < full {}",
            por.num_states(),
            full.num_states()
        );
        assert_eq!(
            reachable_barbs(&full, &[]),
            reachable_barbs(&por, &[]),
            "n={n}: reachable barbs differ"
        );
    }
}

// ---------------------------------------------------------------------------
// Acceptance benchmark: N independent Comms, 2^N full vs linear POR.
// ---------------------------------------------------------------------------

/// A system of `n` genuinely independent Comm pairs on distinct channels, plus a
/// persistent, never-consumed output on an observed channel `o`.
fn independent_bench(n: usize) -> (Proc, Name) {
    let mut comps = Vec::new();
    for k in 0..n {
        // channels 1..=n are distinct and never ⌜0⌝
        comps.extend(comm_pair(distinct_chan(k + 1)));
    }
    let o = distinct_chan(n + 1); // observed, persistent barb
    comps.push(lift(o.clone(), zero()));
    (par(comps), o)
}

#[test]
fn acceptance_exponential_to_linear() {
    let n = 8;
    let (sys, o) = independent_bench(n);
    let observed = [o.clone()];

    let full = Lts::explore(&sys, 1 << 16);
    let por = Lts::explore_por(&sys, 1 << 16, &observed);

    assert!(!full.is_truncated() && !por.is_truncated());

    // Full exploration enumerates every subset of fired pairs: 2^n states.
    assert_eq!(full.num_states(), 1 << n, "full is exponential");
    // POR linearizes the independent pairs: one step per pair.
    assert_eq!(por.num_states(), n + 1, "POR is linear");
    assert!(
        por.num_states() * 20 < full.num_states(),
        "substantial reduction: {} vs {}",
        por.num_states(),
        full.num_states()
    );

    // Identical verdicts on the preserved class.
    let o1 = o.clone();
    let present = move |_name: &str, proc: &Proc| emits(proc, &o1);
    // The observed barb is present throughout, so it is both reachable and
    // invariant — in both the full and the reduced LTS.
    assert!(holds(&full, &ef(prop("b0")), &present));
    assert!(holds(&por, &ef(prop("b0")), &present));
    assert!(holds(&full, &ag(prop("b0")), &present));
    assert!(holds(&por, &ag(prop("b0")), &present));

    // A never-present barb is unreachable in both.
    let ghost = distinct_chan(n + 5);
    let absent = move |_name: &str, proc: &Proc| emits(proc, &ghost);
    assert!(!holds(&full, &ef(prop("b0")), &absent));
    assert!(!holds(&por, &ef(prop("b0")), &absent));

    assert_eq!(
        reachable_barbs(&full, &observed),
        reachable_barbs(&por, &observed)
    );
}
